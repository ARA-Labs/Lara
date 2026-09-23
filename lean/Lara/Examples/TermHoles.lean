/-
# Nested critical-question holes filled by a context

The same policy-local question occurs at two nested rule instances. Distinct
hole identities let the context answer both occurrences independently. The
filled derivation is obtained from template substitution soundness.
-/
import Lara.Examples
import Lara.Examples.Linking
import Lara.Admission
import Lara.Context.Holes.Template
import Lara.Context.Holes.Transport

namespace Lara.Examples.TermHoles

open Lara.Support Lara.Attack Lara.Compile
open Lara.Context.Holes

/-- A defeasible `p`-to-`p` step demanding a complete answer for `q`. -/
def stepRule : Rule :=
  { mode := .defeasible, params := [], premises := [apA], concl := apA
  , questions := [⟨q1, apB, true⟩], allowTrusted := false, certifiers := [] }

/-- The answer `q` can also rebut the nested conclusion `p`. -/
def holePolicy : Policy.Policy :=
  { rules := [⟨rWrapId, stepRule⟩], defeat := dpEx }

/-- The combined evidence environment of the eventual link. -/
def gamma : LeafId → Option Atom := Admission.buildGamma [(l2, pB), (l1, pA)]

/-- Erased inner occurrence: its mandatory question remains open. -/
def innerOpen : SupportTerm := .inst rWrapId [] [.leaf l1] [] [q1] .none

/-- The nested source has the same local question at both occurrences. -/
def nestedOpen : SupportTerm := .inst rWrapId [] [innerOpen] [] [q1] .none

/-- The source is independently typed with a nonempty obligation set. Question
sets intentionally deduplicate equal local names; hole identities will not. -/
theorem source_support :
    HasSupport id holePolicy.ruleLookup gamma (certOkOf registryEx) nestedOpen pA [q1] :=
  Check.inferSupport_sound (loc := .root) (result := ⟨pA, [q1]⟩) rfl

/-- The source really is open. -/
theorem source_obligations_nonempty : [q1] ≠ ([] : List QuestionId) := by decide

/-- The inner and outer occurrence names are globally distinct. -/
def innerHole : HoleId := ⟨"inner-q1"⟩
def outerHole : HoleId := ⟨"outer-q1"⟩

/-- Repeated local question names do not collapse the explicit hole identities. -/
def inner : Template :=
  .inst rWrapId [] [.core (.leaf l1)] [(q1, .hole innerHole)] [] .none

def nested : Template :=
  .inst rWrapId [] [inner] [(q1, .hole outerHole)] [] .none

/-- Both occurrences demand `q`; identity specifies which slot is filled. -/
def signature : HoleSignature := fun h =>
  if h = innerHole ∨ h = outerHole then some pB else none

def innerFilling : Filling := [(innerHole, .leaf l2)]
def outerFilling : Filling := [(outerHole, .leaf l2)]
def fillings : Filling := innerFilling ++ outerFilling

def innerClosed : SupportTerm :=
  .inst rWrapId [] [.leaf l1] [(q1, .leaf l2)] [] .none

def nestedClosed : SupportTerm :=
  .inst rWrapId [] [innerClosed] [(q1, .leaf l2)] [] .none

/-- Erasure produces the independently checked open source. -/
theorem erase_nested : eraseOpen nested = nestedOpen := rfl

/-- Both explicit occurrences receive their own binding. -/
theorem instantiate_nested : instantiate fillings nested = .ok nestedClosed := rfl

/-- The input table has no ambiguity. -/
theorem fillings_nodup : FillingNodup fillings := by unfold FillingNodup; decide

/-- Distinct occurrence identities permit disjoint composition. -/
theorem fillings_disjoint : DisjointFillings innerFilling outerFilling := by
  intro h hi ho
  simp [innerFilling, outerFilling] at hi ho
  subst h
  exact (by decide : innerHole ≠ outerHole) ho

/-- Sequential substitution agrees with the combined context table by the
composition theorem, including the hole below the outer premise boundary. -/
theorem sequential_substitution :
    subst outerFilling (subst innerFilling nested) = subst fillings nested :=
  (subst_append innerFilling outerFilling nested).symm

/-- The combined table closes both occurrences. -/
theorem sequential_instantiation :
    instantiate outerFilling (subst innerFilling nested) = .ok nestedClosed := rfl

/-- Supplying only the inner answer reports the missing outer occurrence. -/
theorem missing_binding :
    instantiate innerFilling nested = .error (.missing outerHole) := rfl

/-- Duplicate identifiers are rejected even if their values happen to agree. -/
theorem duplicate_binding :
    instantiate (innerFilling ++ innerFilling) nested = .error (.duplicate innerHole) := rfl

private theorem step_meta :
    InstMeta id holePolicy.ruleLookup (certOkOf registryEx) rWrapId [] stepRule
      1 [q1] [] .none [pA] [pA] [[]] [pB] [[]] pA where
  rule := rfl
  θNodup := by simp
  θDom := by intro x; simp [stepRule]
  prems := rfl
  concl := rfl
  lenAs := rfl
  lenCs := rfl
  lenOs := rfl
  premEq := by
    intro i A B hA hB
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hA hB
      subst A; subst B; exact equiv_refl _ _
    | succ i => simp at hA
  lenDCs := rfl
  lenDOs := rfl
  ans := by
    intro i q A hq hA
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hq hA
      subst q; subst A
      exact ⟨⟨q1, apB, true⟩, by simp [stepRule], rfl, pB, rfl, equiv_refl _ _⟩
    | succ i => simp at hq
  qNodup := by simp [questionNames, stepRule]
  dNodup := by simp
  hNodup := by simp
  cover := by intro q h; simp [stepRule] at h; subst q; simp
  disj := by simp
  keysD := by simp [questionNames, stepRule]
  keysH := by simp
  strictNoQ := by simp [stepRule]
  assur := .defeasible rfl

private theorem step_template (t : Template) (h : HoleId)
    (ht : HasTemplate id holePolicy.ruleLookup gamma (certOkOf registryEx) signature t pA [])
    (hh : signature h = some pB) :
    HasTemplate id holePolicy.ruleLookup gamma (certOkOf registryEx) signature
      (.inst rWrapId [] [t] [(q1, .hole h)] [] .none) pA [] := by
  apply HasTemplate.inst (As := [pA]) (Cs := [pA]) (Os := [[]])
    (DCs := [pB]) (DOs := [[]]) (r := stepRule) step_meta
  · intro i t' A O hi hA hO
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi hA hO
      subst t'; subst A; subst O
      exact ht
    | succ i => simp at hi
  · intro i q a A O hi hA hO
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi hA hO
      rcases hi with ⟨rfl, rfl⟩
      subst A; subst O
      exact .hole hh
    | succ i => simp at hi

/-- Independent typing of the nested syntax uses rule metadata, recursive
premise typing, and the signature of each explicit hole. -/
theorem template_typed :
    HasTemplate id holePolicy.ruleLookup gamma (certOkOf registryEx) signature nested pA [] :=
  step_template inner outerHole
    (step_template (.core (.leaf l1)) innerHole (.core (.leaf rfl)) (by simp [signature]))
    (by simp [signature])

/-- Every filling supplies its own complete support derivation for the
signature demand, independently of the instantiated whole term. -/
theorem fillings_typed :
    FillingTyped id holePolicy.ruleLookup gamma (certOkOf registryEx) signature fillings := by
  intro h A hh
  unfold signature at hh
  split at hh
  · rename_i hm
    cases Option.some.inj hh
    rcases hm with rfl | rfl
    · exact ⟨.leaf l2, pB, rfl, .leaf rfl, equiv_refl _ _⟩
    · exact ⟨.leaf l2, pB, rfl, .leaf rfl, equiv_refl _ _⟩
  · cases hh

/-- Generic erasure soundness recovers the checked open source, and support
uniqueness pins its nonempty obligation set to the concrete `[q1]`. -/
theorem erased_source_typed :
    HasSupport id holePolicy.ruleLookup gamma (certOkOf registryEx) (eraseOpen nested) pA [q1] := by
  obtain ⟨O, hO⟩ := eraseOpen_hasSupport template_typed
  have hsame := hasSupport_unique hO source_support
  rw [hsame.2] at hO
  exact hO

/-- The filled core derivation is obtained from the substitution theorem,
not supplied as a premise and not inferred by checking the final term. -/
theorem filled_support :
    HasSupport id holePolicy.ruleLookup gamma (certOkOf registryEx) nestedClosed pA [] := by
  obtain ⟨w, hw, hs⟩ := instantiate_hasSupport template_typed fillings_typed fillings_nodup
  rw [instantiate_nested] at hw
  cases Except.ok.inj hw
  exact hs

/-- The instantiated attack is genuinely typed; its target is the filled
nested rule instance, and its source is independently checked evidence. -/
theorem filled_attack_typed :
    HasAttack id holePolicy.ruleLookup gamma (certOkOf registryEx) holePolicy.defeat
      (.rebut (.leaf l2) nestedClosed) :=
  .rebut (.leaf rfl) (r := stepRule) rfl rfl rfl
    ((contraryMatchB_iff id holePolicy.defeat pB pA).mp (by decide))

/-- Fragment metadata and instantiated material at the old checker boundary. -/
def closedFragment : Lara.Context.Fragment :=
  { sigma := sigmaEx, policy := holePolicy, gammaFrag := [(l1, pA)], ground := [pA]
  , args := [.leaf l2, nestedClosed], atts := [.rebut (.leaf l2) nestedClosed]
  , imports := ⟨[l2]⟩, exports := [pA] }

/-- The context provides the answer's evidence leaf. -/
def frame : Lara.Context.Context :=
  ⟨{ sigma := sigmaEx, policy := holePolicy, gammaFrag := [(l2, pB)], ground := [pB]
   , args := [], atts := [], imports := Lara.Context.Interface.closed, exports := [] }⟩

/-- Linked lookup is the same independent environment used in template typing. -/
theorem linked_gamma : Lara.Context.linkGamma frame closedFragment = gamma := rfl

/-- The fully substituted declaration is accepted by the existing checker,
including its actual rebut whose target contains both substituted answers. -/
theorem closed_link_accepted :
    (Check.Unit.checkUnit (Lara.Context.linkGamma frame closedFragment) registryEx
      (Lara.Context.linkGround frame closedFragment)
      (Lara.Context.linkedUnit registryEx frame closedFragment)).isOk = true := by decide

/-- The resulting attack has an endpoint whose outer discharge is supplied
by the context, rather than an unchanged decorative core term. -/
theorem attack_endpoint_discharge :
    Attack.target (.rebut (.leaf l2) nestedClosed) =
      .inst rWrapId [] [innerClosed] [(q1, .leaf l2)] [] .none := rfl

/-- The outer binding is syntactically present but concludes the wrong atom. -/
def wrongFillings : Filling := innerFilling ++ [(outerHole, .leaf l1)]

def wrongClosed : SupportTerm :=
  .inst rWrapId [] [innerClosed] [(q1, .leaf l1)] [] .none

/-- Substitution itself is structural and leaves answer checking to the checker. -/
theorem wrong_answer_instantiates : instantiate wrongFillings nested = .ok wrongClosed := rfl

def wrongFragment : Lara.Context.Fragment :=
  { closedFragment with args := [.leaf l2, wrongClosed], atts := [.rebut (.leaf l2) wrongClosed] }

/-- The detailed existing R6 checker diagnostic survives the new boundary. -/
def wrongAnswerError : Check.Unit.UnitError :=
  .program (.rejection (.argument 1)
    (.R6 (.question .root q1) (.conclusionMismatch q1 pB pA)))

/-- A supplied but ill-typed answer is an old checker rejection, not a missing
hole or hygiene error. -/
theorem wrong_answer_rejected :
    Lara.Context.obs registryEx frame wrongFragment = .rejected wrongAnswerError := by decide

/-- The fragment carries the nested open argument and a template attack
whose target contains the same holes as the declared argument. -/
def templateFragment : HoleFragment :=
  { sigma := sigmaEx, policy := holePolicy, gammaFrag := [(l1, pA)], ground := [pA]
  , imports := ⟨[l2]⟩, exports := [pA], args := [.core (.leaf l2), nested]
  , atts := [.rebut (.core (.leaf l2)) nested] }

/-- The surrounding context supplies both occurrence-specific answers. -/
def context : HoleContext := ⟨frame, fillings⟩

/-- Instantiation reaches precisely the already accepted old fragment. -/
theorem fragment_instantiated : instantiateFragment fillings templateFragment = .ok closedFragment := rfl

/-- Attack substitution traverses the genuine nested endpoint. -/
theorem attack_instantiated :
    instantiateAttack fillings (.rebut (.core (.leaf l2)) nested) =
      .ok (.rebut (.leaf l2) nestedClosed) := rfl

/-- The checked link observes the nested claim as defeated by its complete
answer argument, which is also the source of the declared rebut. -/
theorem hole_observation :
    obs registryEx context templateFragment = .ok (.observed [.defeated]) := rfl

/-- Missing bindings remain distinct from all old linking/checking outcomes. -/
theorem hole_missing :
    obs registryEx ⟨frame, innerFilling⟩ templateFragment = .error (.missing outerHole) := rfl

/-- Binding hygiene is checked before fragment instantiation. -/
theorem hole_duplicate :
    obs registryEx ⟨frame, innerFilling ++ innerFilling⟩ templateFragment =
      .error (.duplicate innerHole) := rfl

/-- Wrong answers preserve the checker's located R6 rejection. -/
theorem hole_wrong_answer :
    obs registryEx ⟨frame, wrongFillings⟩ templateFragment =
      .ok (.rejected wrongAnswerError) := rfl

/-- Sequential partial instantiation agrees at the entire fragment boundary,
including the attack's substituted target. -/
theorem fragment_sequential :
    instantiateFragment outerFilling (substFragment innerFilling templateFragment) =
      instantiateFragment fillings templateFragment := rfl

/-- The second context contributes only the outer answer binding. -/
def outerContext : HoleContext :=
  ⟨⟨{ frame.frame with gammaFrag := [], ground := [] }⟩, outerFilling⟩

def innerContext : HoleContext := ⟨frame, innerFilling⟩

/-- Compatible frames and disjoint filling tables compose through the checked
context-composition theorem. -/
theorem contexts_compose :
    compose innerContext outerContext = .ok (some (composedContext innerContext outerContext)) :=
  compose_eq_some (by unfold FillingNodup; decide) (by unfold FillingNodup; decide)
    fillings_disjoint (by decide)

/-- Evaluating the composed context agrees with the combined filling context. -/
theorem composed_observation :
    obs registryEx (composedContext innerContext outerContext) templateFragment =
      obs registryEx context templateFragment := rfl

/-- A genuinely certified filling for the context-fixing boundary witness. -/
def certificateContext : HoleContext :=
  ⟨Linking.certCtx, [(innerHole, Linking.certArg ndId)]⟩

def certificateSignature : HoleSignature := fun h =>
  if h = innerHole then some pB else none

/-- The sensitive filling is a complete checked derivation, rather than an
ill-typed term manufactured merely to make assurance mapping move. -/
theorem certificate_filling_typed :
    FillingTyped id Linking.certPolicy.ruleLookup
      (Lara.Context.linkGamma Linking.certCtx Linking.certFrag)
      (certOkOf registryEx) certificateSignature certificateContext.filling := by
  intro h A hh
  unfold certificateSignature at hh
  split at hh
  · rename_i he
    subst h
    cases Option.some.inj hh
    exact ⟨Linking.certArg ndId, pB, rfl, Linking.certArg_nd, equiv_refl _ _⟩
  · cases hh

/-- The old context-fixing premise holds for this injective,
acceptance-preserving certificate relabel. Only the new filling can move. -/
theorem certificate_frame_fixed :
    Lara.Context.FixesContext Linking.certSwap certificateContext.frame := ⟨rfl, rfl⟩

private theorem fragment_templates_typed :
    ∀ t ∈ templateFragment.args, ∃ A,
      HasTemplate id holePolicy.ruleLookup gamma (certOkOf registryEx) signature t A [] := by
  intro t ht
  simp only [templateFragment, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact ⟨pB, .core (.leaf rfl)⟩
  · exact ⟨pA, template_typed⟩

private theorem fragment_conflicts :
    AttackComplete id holePolicy.ruleLookup gamma (certOkOf registryEx)
      holePolicy.defeat closedFragment.args closedFragment.atts := by
  intro s hs t ht Cs Ct hCs hCt hcon _
  simp only [closedFragment, List.mem_cons, List.not_mem_nil, or_false] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · have h1 := (hasSupport_unique hCs (HasSupport.leaf (l := l2) (p := pB) rfl)).1
    have h2 := (hasSupport_unique hCt (HasSupport.leaf (l := l2) (p := pB) rfl)).1
    subst Cs; subst Ct
    exact absurd ((contraryMatchB_iff id holePolicy.defeat pB pB).mpr hcon) (by decide)
  · exact Lara.Context.covered_of_mem_attackFor (by simp [closedFragment, Lara.Context.attackFor, nestedClosed])
  · have h1 := (hasSupport_unique hCs filled_support).1
    have h2 := (hasSupport_unique hCt (HasSupport.leaf (l := l2) (p := pB) rfl)).1
    subst Cs; subst Ct
    exact absurd ((contraryMatchB_iff id holePolicy.defeat pA pB).mpr hcon) (by decide)
  · have h1 := (hasSupport_unique hCs filled_support).1
    have h2 := (hasSupport_unique hCt filled_support).1
    subst Cs; subst Ct
    exact absurd ((contraryMatchB_iff id holePolicy.defeat pA pA).mpr hcon) (by decide)

/-- The new checked-link theorem derives acceptance from the independently
typed templates and fillings, together with actual attack coverage. -/
theorem typed_link_checked :
    ∃ accepted, Check.Unit.checkUnit (Lara.Context.linkGamma frame closedFragment) registryEx
      (Lara.Context.linkGround frame closedFragment)
      (Lara.Context.linkedUnit registryEx frame closedFragment) = .ok accepted := by
  apply Lara.Context.Holes.link_checked (C := context) (F := templateFragment)
    (Δ := signature) fragment_instantiated (by decide)
    fragment_templates_typed fillings_typed
  · constructor <;> simp [frame, context, AttackComplete]
  · intro k hk
    have he : k = .rebut (.leaf l2) nestedClosed := by simpa [closedFragment] using hk
    subst k
    exact filled_attack_typed
  · intro k hk
    have he : k = .rebut (.leaf l2) nestedClosed := by simpa [closedFragment] using hk
    subst k
    simp [closedFragment, Attack.source]
  · intro k hk
    have he : k = .rebut (.leaf l2) nestedClosed := by simpa [closedFragment] using hk
    subst k
    simp [closedFragment, Attack.target]
  · exact fragment_conflicts
  · rfl
  · rfl
  · decide
  · exact Policy.firstViolation_none_iff.mp (by decide)

/-- An injective, acceptance-preserving relabel can fix the old frame while
moving a checked answer supplied through the new context field. -/
theorem certificate_filling_moves :
    mapFilling Linking.certSwap certificateContext.filling ≠ certificateContext.filling := by decide

/-- Fixing the old frame alone is insufficient: the new context condition
must also fix the filling terms. -/
theorem certificate_context_not_fixed :
    ¬ Lara.Context.Holes.FixesContext Linking.certSwap certificateContext := by
  intro h
  exact certificate_filling_moves h.filling

private theorem nested_admissible : Lara.Context.Admissible registryEx frame closedFragment where
  guard := by decide
  ctx := by constructor <;> simp [frame, AttackComplete]
  frag := by
    apply sideOk_of_typed fragment_instantiated fragment_templates_typed fillings_typed
    · intro k hk
      have he : k = .rebut (.leaf l2) nestedClosed := by simpa [closedFragment] using hk
      subst k
      exact filled_attack_typed
    · intro k hk
      have he : k = .rebut (.leaf l2) nestedClosed := by simpa [closedFragment] using hk
      subst k
      simp [closedFragment, Attack.source]
    · intro k hk
      have he : k = .rebut (.leaf l2) nestedClosed := by simpa [closedFragment] using hk
      subst k
      simp [closedFragment, Attack.target]
    · exact fragment_conflicts
  signature := rfl
  scope := rfl
  ruleIds := by decide
  policy := Policy.firstViolation_none_iff.mp (by decide)

private theorem nested_context_fixed : FixesContext Linking.certSwap context :=
  ⟨⟨rfl, rfl⟩, rfl⟩

/-- Apply functional semantics-parametric transport to the genuinely open,
filled, attacked fixture. The registry replacement is real and `certSwap` is
globally nonidentity, but this particular template uses only `none` assurances
and leaf fillings, so no certificate moves here. The necessity witness above
separately exercises a certified filling that does move. -/
theorem functional_transport_sem (sem : Semantics.ExtensionSemantics) :
    obsSem sem registryEx context templateFragment =
      obsSem sem Linking.registryWrapped context (mapHoleFragment Linking.certSwap templateFragment) :=
  backend_replacement_congruence_sem sem Linking.certSwap_injective Linking.certSwap_preserving
    fragment_instantiated nested_admissible nested_context_fixed

private theorem nested_graph_related :
    RelTemplate (Lara.Context.graphOf Linking.certSwap) nested nested :=
  .inst (.cons
    (.inst (.cons (.core (.leaf l1)) .nil) (.cons (.hole innerHole) .nil) rfl) .nil)
    (.cons (.hole outerHole) .nil) rfl

private theorem fragment_graph_related :
    RelHoleFragment (Lara.Context.graphOf Linking.certSwap) templateFragment templateFragment where
  sigma := rfl
  policy := rfl
  gammaFrag := rfl
  ground := rfl
  imports := rfl
  exports := rfl
  args := .cons (.core (.leaf l2)) (.cons nested_graph_related .nil)
  atts := .cons (.rebut (.core (.leaf l2)) nested_graph_related) .nil

private theorem context_graph_fixed :
    RelFixesContext (Lara.Context.graphOf Linking.certSwap) context where
  frame := Lara.Context.relFixesContext_graphOf nested_context_fixed.frame
  filling := .cons ⟨rfl, .leaf l2⟩ (.cons ⟨rfl, .leaf l2⟩ .nil)

/-- Apply the relational wrapper itself, retaining its graph injectivity and
preservation premises and deriving the instantiated fragment relation. As in
the functional instance, the nested hole fixture is fixed by this certificate
map; this validates relational transport through filling and attacks, not a
certificate-moving example. -/
theorem relational_transport_sem (sem : Semantics.ExtensionSemantics) :
    obsSem sem registryEx context templateFragment =
      obsSem sem Linking.registryWrapped context templateFragment :=
  backend_replacement_parametricity_sem sem
    (Lara.Context.relInj_graphOf Linking.certSwap_injective)
    (Lara.Context.relPreserving_graphOf Linking.certSwap_preserving)
    fragment_instantiated nested_admissible fragment_graph_related context_graph_fixed

end Lara.Examples.TermHoles
