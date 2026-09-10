/-
Executable witnesses for the outer language's surface syntax (issue #307).

Two fixtures, because the two authoring forms need different material.

**A declared bridge** needs two contexts with *rules*, so the one clause the
elaborator decides is not vacuous: `polSrc` declares `p ← q` and `polTgt`
declares the translation `P ← Q` at the same rule identifier.
`rule_clause_holds` is the positive cell; three negative cells cover the three
ways `ruleOkB` can fail — the target carries nothing at the identifier, the
target carries a *different* rule there, and the declared map cannot translate
the source rule at all.

The two contexts also carry a `Gamma` pair **inside the declared vocabulary**,
so `BridgeObligations` is *discharged* (`obligations_declOK`) rather than taken
as a hypothesis: `bridgeDeclOK` is a real `PW.StructuralBridge` at a concrete
declaration, and `support_transport_declOK` carries a checked support across it
— T6 at a surface-authored bridge, instantiated.

**A posed query** needs worlds, so it reuses `Lara.Examples.PWSorted`'s sorted
frame unchanged. `elab_illSorted` is the fixture that joins the two halves of
#307: an ill-sorted authored claim is a *typing error at authoring time*, named
and located, where PW0 would have sent it to a world and got `gap` back.

`Bridge` and `PW.Form` carry functions and dependent data and so have no
`DecidableEq`; the negative cells go through `bridgeError?` / `formError?`,
which observe the reported error and do. Positive cells are ordinary proofs
routed through `elabBridge_complete` / `elabForm_complete`, which is the
intended way to discharge them — the judgment is the specification.
-/

import Lara.Examples.PWSorted
import Lara.Examples.PWStructural
import Lara.PW.Surface

namespace Lara.Examples.PWSurface

open Lara.Support
open Lara.PW Lara.PW.Instance Lara.PW.Surface
open Lara.Examples Lara.Examples.PW Lara.Examples.PWSorted
open Lara.Grounded (Status)

/-! ### A declared bridge with a non-vacuous rule clause -/

def apP : APat := ⟨⟨"p"⟩, .nil⟩
def apQ : APat := ⟨⟨"q"⟩, .nil⟩
def apPt : APat := ⟨⟨"P"⟩, .nil⟩
def apQt : APat := ⟨⟨"Q"⟩, .nil⟩

/-- The source field's one rule: `p` follows defeasibly from `q`. -/
def ruleSrc : Rule :=
  { mode := .defeasible, params := [], premises := [apQ], concl := apP
  , questions := [], allowTrusted := false, certifiers := [] }

/-- The target field's translation of it, at the same rule identifier — which
is what `StructuralBridge.rule_ok` demands. -/
def ruleTgt : Rule :=
  { mode := .defeasible, params := [], premises := [apQt], concl := apPt
  , questions := [], allowTrusted := false, certifiers := [] }

/-- A rule at the *right identifier* that is not the translation: its premise
was left untranslated. This is the failure mode a weakened `ruleOkB` — one
that only checked that the target resolves *something* at `rn` — would let
through, and it is the whole content of the clause. -/
def ruleTgtWrong : Rule :=
  { mode := .defeasible, params := [], premises := [apQ], concl := apPt
  , questions := [], allowTrusted := false, certifiers := [] }

def ridEx : RuleId := ⟨"r1"⟩

def polSrc : Lara.Policy.Policy := { rules := [⟨ridEx, ruleSrc⟩], defeat := ⟨[], []⟩ }
def polTgt : Lara.Policy.Policy := { rules := [⟨ridEx, ruleTgt⟩], defeat := ⟨[], []⟩ }

/-- A target field that does not carry the rule at all. -/
def polTgtMissing : Lara.Policy.Policy := { rules := [], defeat := ⟨[], []⟩ }

/-- A target field that carries a *different* rule at the same identifier. -/
def polTgtWrong : Lara.Policy.Policy :=
  { rules := [⟨ridEx, ruleTgtWrong⟩], defeat := ⟨[], []⟩ }

/-- The declared symbol map: `p ↦ P`, `q ↦ Q`, and the constructor `z ↦ Z`.
The `.con` entry sits *between* the two `.pred` entries so that both assembly
functions must skip an entry of the other namespace — `predMapOf` past the
constructor to reach `q`, `conMapOf` past `p` to reach `z`. -/
def declSymbols : List SymEntry :=
  [.pred ⟨"p"⟩ ⟨"P"⟩, .con ⟨"z"⟩ ⟨"Z"⟩, .pred ⟨"q"⟩ ⟨"Q"⟩]

/-- The same map with `q` withdrawn: the source rule's premise then has no
translation at all, so `trRule` is `none`. -/
def declSymbolsNoQ : List SymEntry := [.pred ⟨"p"⟩ ⟨"P"⟩]

/-- **The decided clause holds** at the matching target policy. -/
theorem rule_clause_holds :
    ruleOkB (symMapOf declSymbols) polSrc polTgt = true := by decide

/-- **…and fails** when the target does not carry the translated rule. -/
theorem rule_clause_fails :
    ruleOkB (symMapOf declSymbols) polSrc polTgtMissing = false := by decide

/-- **…and fails when the target carries a *different* rule** at the same
identifier. Without this cell a decider that merely checked
`pt.ruleLookup rn ≠ none` would satisfy every fixture in this file, so this is
what pins that `ruleOkB` decides what `ruleOkB_iff` says it decides. -/
theorem rule_clause_fails_mistranslated :
    ruleOkB (symMapOf declSymbols) polSrc polTgtWrong = false := by decide

/-- **…and fails when the source rule does not translate at all.** The third
branch: `trRule = none`, because the declared map has no entry for the
premise's predicate. -/
theorem rule_clause_fails_untranslatable :
    ruleOkB (symMapOf declSymbolsNoQ) polSrc polTgt = false := by decide

/-! ### The declared maps, in both namespaces -/

/-- The two evidence leaves the declaration renames, and their target twins.
The bridge fixture needs its own leaves because the two ends need *different*
`Gamma`s: the point of `leaf_ok` is that the target types the *renamed* leaf at
the *translated* atom. -/
def lSrcP : LeafId := ⟨"e-p"⟩
def lSrcQ : LeafId := ⟨"e-q"⟩
def lTgtP : LeafId := ⟨"e-P"⟩
def lTgtQ : LeafId := ⟨"e-Q"⟩

/-- The declared evidence-leaf renaming. -/
def declLeaves : List LeafEntry := [⟨lSrcP, lTgtP⟩, ⟨lSrcQ, lTgtQ⟩]

/-- The declared leaf renaming is honoured, and undeclared leaves pass
through. -/
theorem leafMap_declared : leafMapOf declLeaves lSrcP = lTgtP := by decide

theorem leafMap_undeclared : leafMapOf declLeaves l3 = l3 := by decide

/-- The predicate half reaches an entry that a `.con` entry shadows in the
list but not in the namespace. -/
theorem predMap_declared_after_con :
    (symMapOf declSymbols).predMap "q" = some "Q" := by decide

/-- **The constructor half is exercised too.** A declared bridge may rename a
data constructor, and `conMapOf` must skip the `.pred` entries to find it. -/
theorem conMap_declared : (symMapOf declSymbols).conMap "z" = some "Z" := by decide

theorem conMap_undeclared : (symMapOf declSymbols).conMap "w" = none := by decide

/-- …and a claim carrying the renamed constructor translates through both
halves at once. -/
theorem trAtom_renames_con :
    trAtom (symMapOf declSymbols) (.atom "p" (.cons (.con "z" .nil) .nil))
      = some (.atom "P" (.cons (.con "Z" .nil) .nil)) := by decide

/-! ### The two contexts, with a `Gamma` pair inside the declared vocabulary -/

/-- The target field's signature: the renamed vocabulary. `StructuralBridge` is
about `Gamma`, the policy and `CertOk`, so the bridge pass never reads this —
it is written so the fixture is a field one could also pose queries in. -/
def sigmaTgtRen : Lara.Sigma.Sigma :=
  { sorts := [], cons := [], preds := [⟨⟨"P"⟩, []⟩, ⟨⟨"Q"⟩, []⟩] }

/-- The translated claims: `τ(p()) = P()`, `τ(q()) = Q()`. -/
def pAt : Atom := .atom "P" .nil
def pBt : Atom := .atom "Q" .nil

/-- Source evidence typing. Both admitted leaves carry claims the declared
symbol map can translate — which is exactly the condition `leaf_ok` needs and
which a `Gamma` mentioning `s` (outside the declaration) would break. -/
def ΓBridgeSrc : LeafId → Option Atom := fun l =>
  if l = lSrcP then some pA else if l = lSrcQ then some pB else none

/-- Target evidence typing: the *renamed* leaves at the *translated* atoms.
Both halves are non-trivial, which is what makes `leaf_ok` a real obligation
here rather than a vacuous one. -/
def ΓBridgeTgt : LeafId → Option Atom := fun l =>
  if l = lTgtP then some pAt else if l = lTgtQ then some pBt else none

/-- No certificate judgment on either side: the fixture's rule is defeasible
with an empty certifier allowlist, so no `AssuranceOk.cert` arm is reachable.
`Examples.PWStructural.bridgeCert` (#224) is where `cert_ok` is discharged off
the identity. -/
def certBridge : BackendId → Digest → CertRef → List Atom → Atom → Prop :=
  fun _ _ _ _ _ => False

def ctxSrc : Context :=
  { canon := id, Gamma := ΓBridgeSrc, CertOk := certBridge
  , sigma := sigmaEx, policy := polSrc }

def ctxTgt : Context :=
  { canon := id, Gamma := ΓBridgeTgt, CertOk := certBridge
  , sigma := sigmaTgtRen, policy := polTgt }

def ctxTgtMissing : Context := { ctxTgt with policy := polTgtMissing }

def ctxTgtWrong : Context := { ctxTgt with policy := polTgtWrong }

/-- The declared environment. It names the bridge and its two contexts, so the
declaration's `id`, `source` and `target` are checked rather than inert;
`canon_shared` is `rfl` here, and is a field rather than a check because
function equality is undecidable. -/
def envOK : BridgeEnv := ⟨⟨"b"⟩, ⟨"src"⟩, ⟨"tgt"⟩, ctxSrc, ctxTgt, rfl⟩

def envMissing : BridgeEnv := ⟨⟨"b"⟩, ⟨"src"⟩, ⟨"tgt"⟩, ctxSrc, ctxTgtMissing, rfl⟩

def envWrong : BridgeEnv := ⟨⟨"b"⟩, ⟨"src"⟩, ⟨"tgt"⟩, ctxSrc, ctxTgtWrong, rfl⟩

/-- The declaration itself, stating all three clauses. Its `id` is the
environment's bridge name and its two context names are the environment's, so
it names the same bridge the query half's `naming` does. -/
def declOK : BridgeDecl :=
  ⟨⟨"b"⟩, ⟨"src"⟩, ⟨"tgt"⟩, declSymbols, declLeaves, Clause.all⟩

/-- A declaration that omits `rule-ok`. -/
def declMissingClause : BridgeDecl :=
  ⟨⟨"b"⟩, ⟨"src"⟩, ⟨"tgt"⟩, declSymbols, declLeaves, [.leafOk, .certOk]⟩

/-- A declaration for a different bridge. -/
def declOtherName : BridgeDecl :=
  ⟨⟨"b2"⟩, ⟨"src"⟩, ⟨"tgt"⟩, declSymbols, declLeaves, Clause.all⟩

/-- A declaration whose source context is not the environment's. -/
def declOtherSource : BridgeDecl :=
  ⟨⟨"b"⟩, ⟨"elsewhere"⟩, ⟨"tgt"⟩, declSymbols, declLeaves, Clause.all⟩

/-- …and whose target is not. -/
def declOtherTarget : BridgeDecl :=
  ⟨⟨"b"⟩, ⟨"src"⟩, ⟨"elsewhere"⟩, declSymbols, declLeaves, Clause.all⟩

/-- The declaration is derivable. `rule_ok` is T6's clause, reached from the
decider through `ruleOkB_iff` — which is the direction the elaborator takes,
and the reason the judgment does not name `ruleOkB`. -/
theorem elaborates_declOK :
    ElaboratesBridge envOK declOK ⟨symMapOf declSymbols, leafMapOf declLeaves⟩ where
  name_eq := rfl
  source_eq := rfl
  target_eq := rfl
  clauses_complete := fun c => Clause.mem_all c
  rule_ok := (ruleOkB_iff (symMapOf declSymbols) polSrc polTgt).mp rule_clause_holds
  sym_eq := rfl
  leafMap_eq := rfl

/-- …and therefore elaborates, by completeness. -/
theorem elabBridge_declOK :
    elabBridge envOK declOK = .ok ⟨symMapOf declSymbols, leafMapOf declLeaves⟩ :=
  elabBridge_complete envOK declOK _ elaborates_declOK

/-- **Negative: an incomplete declaration is rejected**, and the report names
the missing clause. The contract is three clauses; a bridge stating two is not
a structural bridge. -/
theorem elabBridge_missingClause :
    bridgeError? (elabBridge envOK declMissingClause)
      = some (.missingClause .ruleOk) := by decide

/-- **Negative: the decided clause is enforced.** The same declaration against
a target field that does not carry the translated rule is rejected. -/
theorem elabBridge_ruleClauseFails :
    bridgeError? (elabBridge envMissing declOK) = some .ruleClauseFails := by
  decide

/-- …and against a target field carrying a *different* rule at the same
identifier. -/
theorem elabBridge_ruleClauseFails_mistranslated :
    bridgeError? (elabBridge envWrong declOK) = some .ruleClauseFails := by
  decide

/-- **Negative: the declaration's own names are read.** A declaration for
another bridge does not elaborate against this environment — without which a
declaration reading `src → tgt` would elaborate identically against *any*
environment, and the transport theorem below would conclude about whatever
contexts the caller supplied. -/
theorem elabBridge_nameMismatch :
    bridgeError? (elabBridge envOK declOtherName)
      = some (.nameMismatch ⟨"b2"⟩ ⟨"b"⟩) := by decide

theorem elabBridge_sourceMismatch :
    bridgeError? (elabBridge envOK declOtherSource)
      = some (.sourceMismatch ⟨"elsewhere"⟩ ⟨"src"⟩) := by decide

theorem elabBridge_targetMismatch :
    bridgeError? (elabBridge envOK declOtherTarget)
      = some (.targetMismatch ⟨"elsewhere"⟩ ⟨"tgt"⟩) := by decide

/-! ### The declaration is a `StructuralBridge`

The two clauses the elaborator cannot decide are *discharged* here, not
assumed. `leaf_ok` is a real proof: each admitted source leaf carries a claim
the declared symbol map translates, and the target types the renamed leaf at
exactly the translated claim. `cert_ok` is vacuous because this field admits no
certificates at all — the fixture's rule is defeasible with an empty certifier
allowlist, so `AssuranceOk.cert` is unreachable; `PWStructural.bridgeCert` is
where `cert_ok` is discharged off the identity. -/

/-- **The obligations hold at this fixture.** -/
theorem obligations_declOK :
    BridgeObligations ctxSrc.canon ctxSrc.Gamma ctxTgt.Gamma
      ctxSrc.CertOk ctxTgt.CertOk ⟨symMapOf declSymbols, leafMapOf declLeaves⟩ where
  leaf_ok := by
    intro l p h
    have h' : ΓBridgeSrc l = some p := h
    unfold ΓBridgeSrc at h'
    by_cases h1 : l = lSrcP
    · rw [if_pos h1] at h'
      cases h'
      exact ⟨pAt, by decide, by rw [h1]; decide⟩
    · rw [if_neg h1] at h'
      by_cases h2 : l = lSrcQ
      · rw [if_pos h2] at h'
        cases h'
        exact ⟨pBt, by decide, by rw [h2]; decide⟩
      · rw [if_neg h2] at h'
        exact nomatch h'
  cert_ok := fun _ _ _ _ _ _ _ _ _ h => h.elim

/-- **T6's contract, at a surface-authored declaration.** Not a hypothesis and
not a hypothetical: `structuralBridgeOf` applied to the derivation and the
discharged obligations. -/
def bridgeDeclOK :
    StructuralBridge ctxSrc.canon ctxSrc.policy.ruleLookup
      ctxTgt.policy.ruleLookup ctxSrc.Gamma ctxTgt.Gamma
      ctxSrc.CertOk ctxTgt.CertOk :=
  structuralBridgeOf envOK declOK _ elaborates_declOK obligations_declOK

/-- Its two maps are the declared ones — the construction denotes the
declaration, not some other pair. -/
theorem structuralBridge_declOK :
    bridgeDeclOK.sym = symMapOf declSymbols ∧
      bridgeDeclOK.leafMap = leafMapOf declLeaves :=
  ⟨rfl, rfl⟩

/-! ### T6 transported across the declared bridge

`elabBridge_support_transport` is the theorem that carries a checked support
across a *surface-authored* bridge, and the reason `BridgeEnv.canon_shared`
exists. Here it is at the fixture: one instance of the declared rule, its
premise discharged by an admitted leaf. -/

/-- The source support term: one instance of `r1`, its `q` premise discharged
by the admitted leaf, no question discharges, no holes, defeasible. -/
def wDecl : SupportTerm := .inst ridEx [] [.leaf lSrcQ] [] [] .none

/-- The transported term: the same instance over the *renamed* leaf. -/
def wDeclTgt : SupportTerm := .inst ridEx [] [.leaf lTgtQ] [] [] .none

/-- The transport genuinely renames — the target term is not the source one. -/
theorem trSupport_wDecl :
    trSupport (symMapOf declSymbols) (leafMapOf declLeaves) wDecl = some wDeclTgt
      ∧ wDeclTgt ≠ wDecl :=
  ⟨rfl, by decide⟩

/-- The source derivation: `wDecl` supports `p()` completely in the source
field. -/
theorem hasSupport_wDecl :
    HasSupport ctxSrc.canon ctxSrc.policy.ruleLookup ctxSrc.Gamma ctxSrc.CertOk
      wDecl pA [] := by
  have hside : InstSide ctxSrc.canon ctxSrc.policy.ruleLookup ctxSrc.CertOk
      ridEx [] ruleSrc [.leaf lSrcQ] [] [] .none [pB] [pB] [[]] [] [] pA :=
    { rule := by decide
      θNodup := List.nodup_nil
      θDom := fun _ => Iff.rfl
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
          subst hA; subst hB
          exact equiv_refl id _
        | succ j => simp at hA
      lenDCs := rfl
      lenDOs := rfl
      ans := fun _ _ _ _ h => nomatch h
      qNodup := List.nodup_nil
      dNodup := List.nodup_nil
      hNodup := List.nodup_nil
      cover := fun _ h => nomatch h
      disj := fun _ h => nomatch h
      keysD := fun _ h => nomatch h
      keysH := fun _ h => nomatch h
      strictNoQ := fun h => nomatch h
      assur := .defeasible rfl }
  have hleaf : HasSupport ctxSrc.canon ctxSrc.policy.ruleLookup ctxSrc.Gamma
      ctxSrc.CertOk (.leaf lSrcQ) pB [] := .leaf (by decide)
  exact HasSupport.inst (canon := ctxSrc.canon) (Gamma := ctxSrc.Gamma) hside
    (by
      intro i w A O hw hA hO
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hw hA hO
        subst hw; subst hA; subst hO
        exact hleaf
      | succ j => simp at hw)
    (fun _ _ _ _ _ h => nomatch h)

/-- **T6 at a surface-authored bridge, instantiated.** The declared bridge
carries the checked source support to a checked support of the *translated*
claim, with the same (empty) obligation list, in the **target context's own**
checking environment — which is what `canon_shared` buys. -/
theorem support_transport_declOK :
    HasSupport ctxTgt.canon ctxTgt.policy.ruleLookup ctxTgt.Gamma ctxTgt.CertOk
      wDeclTgt pAt [] := by
  obtain ⟨C', hC, h⟩ := elabBridge_support_transport envOK declOK _
    elaborates_declOK obligations_declOK hasSupport_wDecl trSupport_wDecl.1
  have hC' : some pAt = some C' := hC
  cases Option.some.inj hC'
  exact h

/-! ### A posed modal query

Reuses `Lara.Examples.PWSorted.bridgeSorted` — two fields, one bridge, the
identity symbol map — and names its contexts and bridge. -/

/-- The naming of the sorted frame. The round-trip premises are what let the
elaborator decide context identity by comparing `CtxId`s, and what keep an
error report naming the spelling the author wrote. -/
def naming : Naming bridgeSorted where
  ctxName := fun k => match k with
    | .source => ⟨"src"⟩
    | .target => ⟨"tgt"⟩
  bridgeName := fun _ => ⟨"b"⟩
  ctxOf := fun n =>
    if n = ⟨"src"⟩ then some .source
    else if n = ⟨"tgt"⟩ then some .target
    else none
  bridgeOf := fun n => if n = ⟨"b"⟩ then some OneBridge.it else none
  ctxOf_ctxName := by intro κ; cases κ <;> rfl
  bridgeOf_bridgeName := by intro b; cases b; rfl
  bridgeName_of_bridgeOf := by
    intro n b h
    by_cases hn : n = ⟨"b"⟩
    · subst hn; cases b; rfl
    · simp [hn] at h
  ctxName_of_ctxOf := by
    intro n κ h
    by_cases h1 : n = ⟨"src"⟩
    · subst h1; simp at h; subst h; rfl
    · by_cases h2 : n = ⟨"tgt"⟩
      · subst h2; simp [h1] at h; subst h; rfl
      · simp [h1, h2] at h

/-- The authored query: "along bridge `b`, is `q` justified?" -/
def surfaceQuery : SForm := .dia ⟨"b"⟩ (.status Status.justified pB)

/-- The typed formula it denotes. -/
def coreQuery : Form bridgeSorted.frame Field.source :=
  .dia OneBridge.it (.status Status.justified qTgt)

/-- The query is derivable: the bridge resolves and the typed query carries the
authored claim. -/
theorem elaborates_surfaceQuery :
    Elaborates naming (κ := Field.source) surfaceQuery coreQuery := by
  unfold coreQuery surfaceQuery
  refine Elaborates.dia (D := bridgeSorted) (E := naming) (b := OneBridge.it)
    rfl ?_
  exact Elaborates.status (D := bridgeSorted) (E := naming) (κ := Field.target)
    Status.justified pB qTgt rfl

/-- …so the elaborator produces exactly it. -/
theorem elabForm_surfaceQuery :
    elabForm naming Field.source surfaceQuery = .ok coreQuery :=
  elabForm_complete naming elaborates_surfaceQuery

/-- **Preservation, instantiated.** The elaborated formula erases back to the
query that was authored: the typing pass renames nothing. -/
theorem unelab_surfaceQuery : unelab naming coreQuery = surfaceQuery :=
  (elaborates_preserves naming elaborates_surfaceQuery).2

/-- **The two halves of #307, joined.** An ill-sorted authored claim is a
typing error at authoring time, naming the offending predicate — where PW0 had
no choice but to send it to a world and report the `gap` that came back. -/
theorem elab_illSorted :
    formError? (elabForm naming Field.source (.status Status.justified qOfZ))
      = some (.notAQuery ⟨"src"⟩ (.illSortedArguments ⟨"q"⟩)) := by decide

/-- A claim the source field cannot state, likewise. -/
theorem elab_outOfVocabulary :
    formError? (elabForm naming Field.source (.status Status.justified rNullary))
      = some (.notAQuery ⟨"src"⟩ (.undeclaredPredicate ⟨"r"⟩)) := by decide

/-- An undeclared bridge is rejected by name. -/
theorem elab_unknownBridge :
    formError? (elabForm naming Field.source (.box ⟨"nope"⟩ .top))
      = some (.unknownBridge ⟨"nope"⟩) := by decide

/-- **The modality is typed.** Reading `⟨b⟩` from the *target* field is
rejected: the bridge does not start there, and the report says which context
was expected. This is the content of elaborating into an intrinsically typed
`Form` rather than a stringly one. -/
theorem elab_sourceMismatch :
    formError? (elabForm naming Field.target (.dia ⟨"b"⟩ .top))
      = some (.bridgeSourceMismatch ⟨"b"⟩ ⟨"tgt"⟩ ⟨"src"⟩) := by decide

/-- The whole posed query resolves its context name and types its formula. -/
theorem elabPosed_surfaceQuery :
    elabPosed naming ⟨⟨"src"⟩, surfaceQuery⟩ = .ok ⟨Field.source, coreQuery⟩ :=
  (elabPosed_ok_iff naming ⟨⟨"src"⟩, surfaceQuery⟩ Field.source rfl coreQuery).mpr
    elabForm_surfaceQuery

/-- **Negative: the one step `elabPosed` adds can fail.** Resolving the context
name is what `elabForm` does not do, `Naming.ctxOf` is a caller-supplied
partial function, and `unknownContext` is the constructor for its `none` case.
The `Except` equality is fine here — the error side never mentions the
`Sigma`-typed ok payload. -/
theorem elabPosed_unknownContext :
    elabPosed naming ⟨⟨"nope"⟩, surfaceQuery⟩
      = .error (.unknownContext ⟨"nope"⟩) := rfl

/-- **And the elaborated query is true at the source world.** The surface form
reaches a satisfaction fact about the PW0 model, which is what a surface for the
outer language is for. -/
theorem surfaceQuery_holds :
    Sat bridgeSorted.frame (Sorted.cmpVal bridgeSorted) coreQuery wT7src :=
  sorted_dia_q

end Lara.Examples.PWSurface
