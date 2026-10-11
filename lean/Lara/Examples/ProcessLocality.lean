/-
Worked grounded-locality countermodels (issue #22, plan P4).

**Scope: grounded semantics only** (see `Lara.Process.Locality`). Every fixture
runs the *real* checked-source pipeline: two authoritative `Surface.Input`s
through `checkSource`, lifted to one stable-identity carrier by
`Lara.Process.Source.Coordinates`. No graph is hand-built, and every assertion
pins checked identities, checked compiled edges, the executable comparison and a
grounded status, never a bare boolean.

The countermodels, in the plan's order:

* `new_attacker_outside` — `attacker` is a new declaration that attacks into the
  query's old ancestry. The test fails, the status changes, and both refuted
  criteria pass (see below).
* `discharge_propagation` — a new attacker undermines a leaf reached through a
  *discharge subterm* shared by the support argument: the closure edge
  (`Compile.containsB`) lands on the support. The test fails, the status changes.
* `node_deletion` — removing the support's defender changes the status; the
  removed node lies in the support's own ancestry region, so correspondence
  fails.
* `complete_support_from_hole` — an argument for the query is a hole before and a
  complete node after: the support set itself changes (`gap` → `justified`).
* `unrelated_self_attack` — a self-attacking node outside every queried ancestor
  leaves the grounded status alone while node and edge differences are nonempty
  (`attacked` → `self`). `scope_stable_differs` shows the same edit does destroy
  stable-extension existence, which is why the certificate claims grounded
  semantics only.
* `unchanged_despite_failure` — changes inside the region cancel: `minimal` and
  `defended` are both `justified` although the test fails, pinning the
  certificate as sufficient-only.

Two deliberately weaker criteria are refuted by the first countermodel:
`rawSupportNames` (the queried supports agree as raw declaration names) and
`oldRegionCriterion` (no changed node and no changed edge *internal* to the old
ancestry region). Both pass while the status moves, because neither sees a new
attacker standing outside the region and attacking into it.

The export/reindex invariants are pinned on the same checked material:
`minimal_label_reindex` moves the carrier, and `permuted_status` reorders the
declarations, both with the query atom held fixed.
-/

import Lara.Process.Locality
import Lara.Examples.ProcessSource

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option pp.deepTerms false

namespace Lara.Examples.ProcessLocality

open Lara Lara.Process Lara.Process.Source Lara.Process.Locality
open Lara.Grounded
open Lara.Examples.ProcessSource

/-! ### Fixture vocabulary -/

/-- The fixed query atom. Every fixture queries this exact atom, never a claim
label. -/
def query : Atom := .atom "t" .nil

/-- A defeasible rule with no questions. -/
def rule (name premise conclusion : String) : Presentation.Rule :=
  { id := ⟨name⟩, params := [], mode := .defeasible, premises := [⟨premise, .nil⟩],
    premiseLabels := [], conclusion := ⟨conclusion, .nil⟩, allowTrusted := false,
    certifiers := [], questions := [] }

/-- A defeasible rule with one mandatory question `question` answered by
`answer`, and no premises. -/
def ruleQ (name conclusion question answer : String) : Presentation.Rule :=
  { id := ⟨name⟩, params := [], mode := .defeasible, premises := [],
    premiseLabels := [], conclusion := ⟨conclusion, .nil⟩, allowTrusted := false,
    certifiers := [], questions := [⟨⟨question⟩, ⟨answer, .nil⟩, .mandatory⟩] }

/-- An observed user-supplied leaf. -/
def leaf (name : String) : Presentation.Leaf :=
  ⟨⟨name⟩, .atom name .nil, .observed, .user, [], none⟩

/-- The argument instantiated by `r-w`, used for the unrelated self-attack. -/
def loopArg : Presentation.Decl :=
  .arg ⟨⟨"loop"⟩, .supportsDerived ⟨"loop-claim"⟩,
    .inferTheta ⟨"r-w"⟩ [⟨"seed"⟩] [] [] .none⟩

def claimDecl : Presentation.Decl :=
  .claim ⟨⟨"claim"⟩, "Target", query, ⟨"reader", "target interpretation", .reviewed⟩⟩

/-- An argument concluding the query atom `t` by rule `r-t`. -/
def witnessArg : Presentation.Decl :=
  .arg ⟨⟨"witness"⟩, .supportsClaim ⟨"claim"⟩, .inferTheta ⟨"r-t"⟩ [⟨"seed"⟩] [] [] .none⟩

/-- An argument concluding the contrary `s` by rule `r-s`. -/
def attackerArg : Presentation.Decl :=
  .arg ⟨⟨"attacker"⟩, .supportsDerived ⟨"attack-claim"⟩,
    .inferTheta ⟨"r-s"⟩ [⟨"seed"⟩] [] [] .none⟩

/-- An argument concluding the contrary `u` of `s` by rule `r-u`. -/
def defenderArg : Presentation.Decl :=
  .arg ⟨⟨"defender"⟩, .supportsDerived ⟨"defense-claim"⟩,
    .inferTheta ⟨"r-u"⟩ [⟨"seed"⟩] [] [] .none⟩

/-- A consumer of the query support: the support term occurs as its premise, so
every attack on the support closes onto the consumer too. -/
def consumerArg : Presentation.Decl :=
  .arg ⟨⟨"consumer"⟩, .supportsDerived ⟨"consumer-claim"⟩,
    .inferTheta ⟨"r-v"⟩ [⟨"witness"⟩] [] [] .none⟩

/-- The fixture policy: exactly the predicates, rules and contraries the
fixture uses, so each kernel-checked acceptance stays small. -/
def policyFor (preds : List Presentation.PredSig) (contraries : List Presentation.Contrary)
    (rules : List Presentation.Rule) : Presentation.Policy :=
  { ProcessSource.ordinaryInput.policy with
    sigma := ⟨[], [], preds⟩
    rules
    contraries
    theories := [] }

def sourceFor (policy : Presentation.Policy) (decls : List Presentation.Decl) : SourceInput :=
  { surface :=
      { ProcessSource.ordinaryInput with
        policy
        program := { ProcessSource.ordinaryInput.program with
          policy := policy.id, backends := [], decls } }
    replay :=
      { core := ⟨Driver.coreVersionText⟩, policy := policy.id, backends := [], theories := [],
        artifact := ProcessSource.ordinaryInput.program.digest }
    capture := none }

def contraryST : Presentation.Contrary := ⟨⟨"s", .nil⟩, ⟨"t", .nil⟩⟩
def contraryUS : Presentation.Contrary := ⟨⟨"u", .nil⟩, ⟨"s", .nil⟩⟩
def contrarySD : Presentation.Contrary := ⟨⟨"s", .nil⟩, ⟨"dseed", .nil⟩⟩
def contraryWW : Presentation.Contrary := ⟨⟨"w", .nil⟩, ⟨"w", .nil⟩⟩

def seedPred : Presentation.PredSig := ⟨⟨"seed"⟩, []⟩
def tPred : Presentation.PredSig := ⟨⟨"t"⟩, []⟩
def sPred : Presentation.PredSig := ⟨⟨"s"⟩, []⟩
def uPred : Presentation.PredSig := ⟨⟨"u"⟩, []⟩
def vPred : Presentation.PredSig := ⟨⟨"v"⟩, []⟩
def wPred : Presentation.PredSig := ⟨⟨"w"⟩, []⟩
def answerPred : Presentation.PredSig := ⟨⟨"answer"⟩, []⟩
def dseedPred : Presentation.PredSig := ⟨⟨"dseed"⟩, []⟩

def witnessRule : Presentation.Rule := rule "r-t" "seed" "t"
def attackerRule : Presentation.Rule := rule "r-s" "seed" "s"
def defenderRule : Presentation.Rule := rule "r-u" "seed" "u"
def consumerRule : Presentation.Rule := rule "r-v" "t" "v"
def loopRule : Presentation.Rule := rule "r-w" "seed" "w"
def dischargerRule : Presentation.Rule := rule "r-e" "dseed" "answer"
def dischargeWrapperRule : Presentation.Rule := ruleQ "r-d" "t" "qd" "answer"
def holeWrapperRule : Presentation.Rule := ruleQ "r-h" "t" "qh" "answer"

/-! ### The four basic checked sources

`minimal` supports the query with an unattacked argument. `attacked` adds an
attacker, `defended` adds the attacker's defender, `self` adds an unrelated
self-attacking argument on top of `attacked`. -/

def minimalDecls : List Presentation.Decl :=
  [.leaf (leaf "seed"), claimDecl, witnessArg, consumerArg]

def attackedDecls : List Presentation.Decl :=
  minimalDecls ++ [attackerArg, .attack (.rebut ⟨"attacker"⟩ ⟨"witness"⟩)]

def defendedDecls : List Presentation.Decl :=
  attackedDecls ++ [defenderArg, .attack (.rebut ⟨"defender"⟩ ⟨"attacker"⟩)]

def selfDecls : List Presentation.Decl :=
  attackedDecls ++ [loopArg, .attack (.rebut ⟨"loop"⟩ ⟨"loop"⟩)]

def minimalInput : SourceInput :=
  sourceFor (policyFor [seedPred, tPred, vPred] [] [witnessRule, consumerRule]) minimalDecls

def attackedInput : SourceInput :=
  sourceFor (policyFor [seedPred, tPred, sPred, vPred] [contraryST]
    [witnessRule, attackerRule, consumerRule]) attackedDecls

def defendedInput : SourceInput :=
  sourceFor (policyFor [seedPred, tPred, sPred, uPred, vPred] [contraryST, contraryUS]
    [witnessRule, attackerRule, defenderRule, consumerRule]) defendedDecls

def selfInput : SourceInput :=
  sourceFor (policyFor [seedPred, tPred, sPred, vPred, wPred] [contraryST, contraryWW]
    [witnessRule, attackerRule, consumerRule, loopRule]) selfDecls

/-! ### The discharge and hole sources -/

def dseedLeaf : Presentation.Leaf := leaf "dseed"

def dischargerArg : Presentation.Decl :=
  .arg ⟨⟨"discharger"⟩, .supportsDerived ⟨"answer-claim"⟩,
    .inferTheta ⟨"r-e"⟩ [⟨"dseed"⟩] [] [] .none⟩

/-- Discharges the question `qd` with `discharger`. -/
def wrapperArg : Presentation.Decl :=
  .arg ⟨⟨"wrapper"⟩, .supportsClaim ⟨"claim"⟩,
    .inferTheta ⟨"r-d"⟩ [] [⟨⟨"qd"⟩, ⟨"discharger"⟩⟩] [] .none⟩

/-- An argument for the query whose mandatory question is open: a hole. -/
def holeArg : Presentation.Decl :=
  .arg ⟨⟨"wrapper"⟩, .supportsClaim ⟨"claim"⟩,
    .inferTheta ⟨"r-h"⟩ [] [] [⟨"qh"⟩] .none⟩

/-- The same wrapper as `holeArg`, with its question discharged by `discharger`. -/
def filledWrapperArg : Presentation.Decl :=
  .arg ⟨⟨"wrapper"⟩, .supportsClaim ⟨"claim"⟩,
    .inferTheta ⟨"r-h"⟩ [] [⟨⟨"qh"⟩, ⟨"discharger"⟩⟩] [] .none⟩

def dischargePolicy : Presentation.Policy :=
  policyFor [seedPred, dseedPred, answerPred, tPred, sPred] [contraryST, contrarySD]
    [dischargerRule, dischargeWrapperRule, attackerRule]

/-- The same declarations in both discharge fixtures, so the only difference is
the appended attacker and its attack. -/
def dischargeBaseDecls : List Presentation.Decl :=
  [.leaf (leaf "seed"), .leaf dseedLeaf, claimDecl, dischargerArg, wrapperArg]

/-- The attacker undermines the leaf inside `wrapper`'s **discharge** subterm:
`Contains` closure (`Compile.containsB`) then lands the edge on `wrapper`
itself, not only on the discharged occurrence. -/
def dischargeAttackDecls : List Presentation.Decl :=
  dischargeBaseDecls ++ [attackerArg,
    .attack (.undermine ⟨"attacker"⟩ ⟨"wrapper"⟩ [.name "qd", .index 0])]

def dischargeBaseInput : SourceInput := sourceFor dischargePolicy dischargeBaseDecls

def dischargeAttackInput : SourceInput := sourceFor dischargePolicy dischargeAttackDecls

def holePolicy : Presentation.Policy :=
  policyFor [dseedPred, answerPred, tPred] [] [dischargerRule, holeWrapperRule]

def holeInput : SourceInput :=
  sourceFor holePolicy [.leaf dseedLeaf, claimDecl, holeArg]

def filledInput : SourceInput :=
  sourceFor holePolicy [.leaf dseedLeaf, claimDecl, dischargerArg, filledWrapperArg]

/-! ### Acceptance through the real pipeline -/

theorem minimal_accepted : (checkSource minimalInput).isOk = true := by decide +kernel

theorem attacked_accepted : (checkSource attackedInput).isOk = true := by decide +kernel

theorem defended_accepted : (checkSource defendedInput).isOk = true := by decide +kernel

theorem self_accepted : (checkSource selfInput).isOk = true := by decide +kernel

theorem dischargeBase_accepted : (checkSource dischargeBaseInput).isOk = true := by
  decide +kernel

theorem dischargeAttack_accepted : (checkSource dischargeAttackInput).isOk = true := by
  decide +kernel

theorem hole_accepted : (checkSource holeInput).isOk = true := by decide +kernel

theorem filled_accepted : (checkSource filledInput).isOk = true := by decide +kernel

/-- The exact accepted observation, bound once per fixture so no later proof
re-derives it inside a larger aggregate. -/
def accept (input : SourceInput) (ok : (checkSource input).isOk = true) :
    AcceptedObservation input :=
  (checkSource input).toOption.get (by
    cases equation : checkSource input with
    | error error => rw [equation] at ok; contradiction
    | ok observation => rfl)

def minimalObs : AcceptedObservation minimalInput := accept minimalInput minimal_accepted
def attackedObs : AcceptedObservation attackedInput := accept attackedInput attacked_accepted
def defendedObs : AcceptedObservation defendedInput := accept defendedInput defended_accepted
def selfObs : AcceptedObservation selfInput := accept selfInput self_accepted
def dischargeBaseObs : AcceptedObservation dischargeBaseInput :=
  accept dischargeBaseInput dischargeBase_accepted
def dischargeAttackObs : AcceptedObservation dischargeAttackInput :=
  accept dischargeAttackInput dischargeAttack_accepted
def holeObs : AcceptedObservation holeInput := accept holeInput hole_accepted
def filledObs : AcceptedObservation filledInput := accept filledInput filled_accepted

/-- The shared stable-identity carrier, in a fixed order. Every label below is
read at a position of this list, never at a declaration index. -/
def carrier : List Presentation.ArgId :=
  [⟨"seed"⟩, ⟨"dseed"⟩, ⟨"witness"⟩, ⟨"attacker"⟩, ⟨"defender"⟩, ⟨"consumer"⟩,
   ⟨"discharger"⟩, ⟨"wrapper"⟩, ⟨"loop"⟩]

def witI : Nat := carrier.idxOf ⟨"witness"⟩
def attI : Nat := carrier.idxOf ⟨"attacker"⟩
def defI : Nat := carrier.idxOf ⟨"defender"⟩
def conI : Nat := carrier.idxOf ⟨"consumer"⟩
def disI : Nat := carrier.idxOf ⟨"discharger"⟩
def wrapI : Nat := carrier.idxOf ⟨"wrapper"⟩
def loopI : Nat := carrier.idxOf ⟨"loop"⟩

/-- The lifted graph of an accepted observation on the shared carrier. -/
abbrev obsGraph {input : SourceInput} (obs : AcceptedObservation input) : Grounded.AF :=
  Coordinates.graph obs.run carrier

/-- The queried support of an accepted observation, as carrier positions. -/
abbrev obsSupport {input : SourceInput} (obs : AcceptedObservation input) :
    List Lara.Process.Locality.Node :=
  querySupport obs.run carrier query

/-- The complete claim of an accepted observation at the fixed query. -/
abbrev obsClaim {input : SourceInput} (obs : AcceptedObservation input) : Grounded.Claim :=
  claimOf obs.run carrier query

/-- The executable comparison of two accepted observations. -/
abbrev obsCheck {first second : SourceInput} (before : AcceptedObservation first)
    (after : AcceptedObservation second) :=
  checkLocality (obsGraph before) (obsGraph after) (obsSupport before) (obsSupport after)


/-- The same declarations with the argument declarations reordered: the checked
indices shift, so only the stable identity aligns the two graphs. -/
def permutedInput : SourceInput :=
  sourceFor (policyFor [seedPred, tPred, sPred, uPred, vPred] [contraryST, contraryUS]
    [witnessRule, attackerRule, defenderRule, consumerRule])
    [.leaf (leaf "seed"), claimDecl, attackerArg, defenderArg, witnessArg, consumerArg,
     .attack (.rebut ⟨"attacker"⟩ ⟨"witness"⟩),
     .attack (.rebut ⟨"defender"⟩ ⟨"attacker"⟩)]

theorem permuted_accepted : (checkSource permutedInput).isOk = true := by decide +kernel

def permutedObs : AcceptedObservation permutedInput := accept permutedInput permuted_accepted

/-! ### Checked values, one equation per fixture

Each fixture pins a single concrete value — its queried support names, its
compiled carrier, its compiled edges, its queried support, its incoming-attacker
table and its grounded status — in **one** kernel-checked equation. Every per-row
fact below is read off that equation by projection and list indexing, so no
observation is evaluated twice.

`decide +kernel` is used rather than `rfl`: on these terms the kernel's compiled
decision procedure finishes in a fraction of a second, while the definitional
unfolding `rfl` triggers does not terminate within 75 s at ~6 GB (measured on the
minimal aggregate). Carrier positions: seed `0`, dseed `1`, witness `2`, attacker
`3`, defender `4`, consumer `5`, discharger `6`, wrapper `7`, loop `8`. -/

private structure CheckedValues where
  supportNames : List Presentation.ArgId
  args : List Node
  edgeList : List (Node × Node)
  support : List Node
  incomingRows : List (Node × List Node)
  status : Status
deriving DecidableEq

/-- Read one incoming-attacker row off the pinned table. -/
private theorem incoming_of_rows {F : AF} {as : List Node} {rows : List (Node × List Node)}
    {i : Nat} {a : Node} {l : List Node}
    (ha : F.args = as) (hr : F.args.map (fun x => (x, incoming F x)) = rows)
    (hia : as[i]? = some a) (hir : rows[i]? = some (a, l)) : incoming F a = l := by
  have h : (as.map (fun x => (x, incoming F x)))[i]? = rows[i]? := by rw [← ha, hr]
  rw [List.getElem?_map, hia, hir] at h
  simpa using h


private def minimalValues : CheckedValues :=
  { supportNames := Coordinates.supports minimalObs.run query
    args := (obsGraph minimalObs).args
    edgeList := edges (obsGraph minimalObs)
    support := obsSupport minimalObs
    incomingRows := (obsGraph minimalObs).args.map fun a => (a, incoming (obsGraph minimalObs) a)
    status := statusC (obsGraph minimalObs) (obsClaim minimalObs) }

private theorem minimalValues_eq :
    minimalValues =
      ({ supportNames := [⟨"witness"⟩], args := [witI, conI], edgeList := [], support := [witI],
         incomingRows := [(witI, []), (conI, [])], status := .justified } : CheckedValues) := by
  decide +kernel


private def attackedValues : CheckedValues :=
  { supportNames := Coordinates.supports attackedObs.run query
    args := (obsGraph attackedObs).args
    edgeList := edges (obsGraph attackedObs)
    support := obsSupport attackedObs
    incomingRows := (obsGraph attackedObs).args.map fun a => (a, incoming (obsGraph attackedObs) a)
    status := statusC (obsGraph attackedObs) (obsClaim attackedObs) }

private theorem attackedValues_eq :
    attackedValues =
      ({ supportNames := [⟨"witness"⟩], args := [witI, conI, attI], edgeList := [(attI, witI), (attI, conI)], support := [witI],
         incomingRows := [(witI, [attI]), (conI, [attI]), (attI, [])], status := .defeated } : CheckedValues) := by
  decide +kernel


private def defendedValues : CheckedValues :=
  { supportNames := Coordinates.supports defendedObs.run query
    args := (obsGraph defendedObs).args
    edgeList := edges (obsGraph defendedObs)
    support := obsSupport defendedObs
    incomingRows := (obsGraph defendedObs).args.map fun a => (a, incoming (obsGraph defendedObs) a)
    status := statusC (obsGraph defendedObs) (obsClaim defendedObs) }

private theorem defendedValues_eq :
    defendedValues =
      ({ supportNames := [⟨"witness"⟩], args := [witI, conI, attI, defI], edgeList := [(attI, witI), (attI, conI), (defI, attI)], support := [witI],
         incomingRows := [(witI, [attI]), (conI, [attI]), (attI, [defI]), (defI, [])], status := .justified } : CheckedValues) := by
  decide +kernel


private def selfValues : CheckedValues :=
  { supportNames := Coordinates.supports selfObs.run query
    args := (obsGraph selfObs).args
    edgeList := edges (obsGraph selfObs)
    support := obsSupport selfObs
    incomingRows := (obsGraph selfObs).args.map fun a => (a, incoming (obsGraph selfObs) a)
    status := statusC (obsGraph selfObs) (obsClaim selfObs) }

private theorem selfValues_eq :
    selfValues =
      ({ supportNames := [⟨"witness"⟩], args := [witI, conI, attI, loopI], edgeList := [(attI, witI), (attI, conI), (loopI, loopI)], support := [witI],
         incomingRows := [(witI, [attI]), (conI, [attI]), (attI, []), (loopI, [loopI])], status := .defeated } : CheckedValues) := by
  decide +kernel


private def dischargeBaseValues : CheckedValues :=
  { supportNames := Coordinates.supports dischargeBaseObs.run query
    args := (obsGraph dischargeBaseObs).args
    edgeList := edges (obsGraph dischargeBaseObs)
    support := obsSupport dischargeBaseObs
    incomingRows := (obsGraph dischargeBaseObs).args.map fun a => (a, incoming (obsGraph dischargeBaseObs) a)
    status := statusC (obsGraph dischargeBaseObs) (obsClaim dischargeBaseObs) }

private theorem dischargeBaseValues_eq :
    dischargeBaseValues =
      ({ supportNames := [⟨"wrapper"⟩], args := [disI, wrapI], edgeList := [], support := [wrapI],
         incomingRows := [(disI, []), (wrapI, [])], status := .justified } : CheckedValues) := by
  decide +kernel


private def dischargeAttackValues : CheckedValues :=
  { supportNames := Coordinates.supports dischargeAttackObs.run query
    args := (obsGraph dischargeAttackObs).args
    edgeList := edges (obsGraph dischargeAttackObs)
    support := obsSupport dischargeAttackObs
    incomingRows := (obsGraph dischargeAttackObs).args.map fun a => (a, incoming (obsGraph dischargeAttackObs) a)
    status := statusC (obsGraph dischargeAttackObs) (obsClaim dischargeAttackObs) }

private theorem dischargeAttackValues_eq :
    dischargeAttackValues =
      ({ supportNames := [⟨"wrapper"⟩], args := [disI, wrapI, attI], edgeList := [(attI, disI), (attI, wrapI)], support := [wrapI],
         incomingRows := [(disI, [attI]), (wrapI, [attI]), (attI, [])], status := .defeated } : CheckedValues) := by
  decide +kernel


private def holeValues : CheckedValues :=
  { supportNames := Coordinates.supports holeObs.run query
    args := (obsGraph holeObs).args
    edgeList := edges (obsGraph holeObs)
    support := obsSupport holeObs
    incomingRows := (obsGraph holeObs).args.map fun a => (a, incoming (obsGraph holeObs) a)
    status := statusC (obsGraph holeObs) (obsClaim holeObs) }

private theorem holeValues_eq :
    holeValues =
      ({ supportNames := [], args := [], edgeList := [], support := [],
         incomingRows := [], status := .gap } : CheckedValues) := by
  decide +kernel


private def filledValues : CheckedValues :=
  { supportNames := Coordinates.supports filledObs.run query
    args := (obsGraph filledObs).args
    edgeList := edges (obsGraph filledObs)
    support := obsSupport filledObs
    incomingRows := (obsGraph filledObs).args.map fun a => (a, incoming (obsGraph filledObs) a)
    status := statusC (obsGraph filledObs) (obsClaim filledObs) }

private theorem filledValues_eq :
    filledValues =
      ({ supportNames := [⟨"wrapper"⟩], args := [disI, wrapI], edgeList := [], support := [wrapI],
         incomingRows := [(disI, []), (wrapI, [])], status := .justified } : CheckedValues) := by
  decide +kernel


private def permutedValues : CheckedValues :=
  { supportNames := Coordinates.supports permutedObs.run query
    args := (obsGraph permutedObs).args
    edgeList := edges (obsGraph permutedObs)
    support := obsSupport permutedObs
    incomingRows := (obsGraph permutedObs).args.map fun a => (a, incoming (obsGraph permutedObs) a)
    status := statusC (obsGraph permutedObs) (obsClaim permutedObs) }

private theorem permutedValues_eq :
    permutedValues =
      ({ supportNames := [⟨"witness"⟩], args := [attI, defI, witI, conI], edgeList := [(attI, witI), (attI, conI), (defI, attI)], support := [witI],
         incomingRows := [(attI, [defI]), (defI, []), (witI, [attI]), (conI, [attI])], status := .justified } : CheckedValues) := by
  decide +kernel


/-! #### Per-row facts, projected out of the pinned equation -/


private theorem minimalIncomingRows :
    (obsGraph minimalObs).args.map (fun a => (a, incoming (obsGraph minimalObs) a)) = [(witI, []), (conI, [])] := by
  simpa [minimalValues] using congrArg CheckedValues.incomingRows minimalValues_eq


theorem minimal_supportNames :
    Coordinates.supports minimalObs.run query = [⟨"witness"⟩] := by
  simpa [minimalValues] using congrArg CheckedValues.supportNames minimalValues_eq


theorem minimal_support :
    obsSupport minimalObs = [witI] := by
  simpa [minimalValues] using congrArg CheckedValues.support minimalValues_eq


private theorem attackedIncomingRows :
    (obsGraph attackedObs).args.map (fun a => (a, incoming (obsGraph attackedObs) a)) = [(witI, [attI]), (conI, [attI]), (attI, [])] := by
  simpa [attackedValues] using congrArg CheckedValues.incomingRows attackedValues_eq


theorem attacked_supportNames :
    Coordinates.supports attackedObs.run query = [⟨"witness"⟩] := by
  simpa [attackedValues] using congrArg CheckedValues.supportNames attackedValues_eq


theorem attacked_support :
    obsSupport attackedObs = [witI] := by
  simpa [attackedValues] using congrArg CheckedValues.support attackedValues_eq


theorem attacked_edges :
    edges (obsGraph attackedObs) = [(attI, witI), (attI, conI)] := by
  simpa [attackedValues] using congrArg CheckedValues.edgeList attackedValues_eq


theorem attacked_args :
    (obsGraph attackedObs).args = [witI, conI, attI] := by
  simpa [attackedValues] using congrArg CheckedValues.args attackedValues_eq


private theorem defendedIncomingRows :
    (obsGraph defendedObs).args.map (fun a => (a, incoming (obsGraph defendedObs) a)) = [(witI, [attI]), (conI, [attI]), (attI, [defI]), (defI, [])] := by
  simpa [defendedValues] using congrArg CheckedValues.incomingRows defendedValues_eq


theorem defended_supportNames :
    Coordinates.supports defendedObs.run query = [⟨"witness"⟩] := by
  simpa [defendedValues] using congrArg CheckedValues.supportNames defendedValues_eq


theorem defended_support :
    obsSupport defendedObs = [witI] := by
  simpa [defendedValues] using congrArg CheckedValues.support defendedValues_eq


private theorem selfIncomingRows :
    (obsGraph selfObs).args.map (fun a => (a, incoming (obsGraph selfObs) a)) = [(witI, [attI]), (conI, [attI]), (attI, []), (loopI, [loopI])] := by
  simpa [selfValues] using congrArg CheckedValues.incomingRows selfValues_eq


theorem self_supportNames :
    Coordinates.supports selfObs.run query = [⟨"witness"⟩] := by
  simpa [selfValues] using congrArg CheckedValues.supportNames selfValues_eq


theorem self_support :
    obsSupport selfObs = [witI] := by
  simpa [selfValues] using congrArg CheckedValues.support selfValues_eq


theorem self_edges :
    edges (obsGraph selfObs) = [(attI, witI), (attI, conI), (loopI, loopI)] := by
  simpa [selfValues] using congrArg CheckedValues.edgeList selfValues_eq


theorem self_args :
    (obsGraph selfObs).args = [witI, conI, attI, loopI] := by
  simpa [selfValues] using congrArg CheckedValues.args selfValues_eq


private theorem dischargeBaseIncomingRows :
    (obsGraph dischargeBaseObs).args.map (fun a => (a, incoming (obsGraph dischargeBaseObs) a)) = [(disI, []), (wrapI, [])] := by
  simpa [dischargeBaseValues] using congrArg CheckedValues.incomingRows dischargeBaseValues_eq


theorem dischargeBase_supportNames :
    Coordinates.supports dischargeBaseObs.run query = [⟨"wrapper"⟩] := by
  simpa [dischargeBaseValues] using congrArg CheckedValues.supportNames dischargeBaseValues_eq


theorem dischargeBase_support :
    obsSupport dischargeBaseObs = [wrapI] := by
  simpa [dischargeBaseValues] using congrArg CheckedValues.support dischargeBaseValues_eq


private theorem dischargeAttackIncomingRows :
    (obsGraph dischargeAttackObs).args.map (fun a => (a, incoming (obsGraph dischargeAttackObs) a)) = [(disI, [attI]), (wrapI, [attI]), (attI, [])] := by
  simpa [dischargeAttackValues] using congrArg CheckedValues.incomingRows dischargeAttackValues_eq


theorem dischargeAttack_supportNames :
    Coordinates.supports dischargeAttackObs.run query = [⟨"wrapper"⟩] := by
  simpa [dischargeAttackValues] using congrArg CheckedValues.supportNames dischargeAttackValues_eq


theorem dischargeAttack_support :
    obsSupport dischargeAttackObs = [wrapI] := by
  simpa [dischargeAttackValues] using congrArg CheckedValues.support dischargeAttackValues_eq


theorem dischargeAttack_edges :
    edges (obsGraph dischargeAttackObs) = [(attI, disI), (attI, wrapI)] := by
  simpa [dischargeAttackValues] using congrArg CheckedValues.edgeList dischargeAttackValues_eq


theorem hole_supportNames :
    Coordinates.supports holeObs.run query = [] := by
  simpa [holeValues] using congrArg CheckedValues.supportNames holeValues_eq


theorem hole_support :
    obsSupport holeObs = [] := by
  simpa [holeValues] using congrArg CheckedValues.support holeValues_eq


private theorem filledIncomingRows :
    (obsGraph filledObs).args.map (fun a => (a, incoming (obsGraph filledObs) a)) = [(disI, []), (wrapI, [])] := by
  simpa [filledValues] using congrArg CheckedValues.incomingRows filledValues_eq


theorem filled_supportNames :
    Coordinates.supports filledObs.run query = [⟨"wrapper"⟩] := by
  simpa [filledValues] using congrArg CheckedValues.supportNames filledValues_eq


theorem filled_support :
    obsSupport filledObs = [wrapI] := by
  simpa [filledValues] using congrArg CheckedValues.support filledValues_eq


theorem permuted_supportNames :
    Coordinates.supports permutedObs.run query = [⟨"witness"⟩] := by
  simpa [permutedValues] using congrArg CheckedValues.supportNames permutedValues_eq


theorem permuted_support :
    obsSupport permutedObs = [witI] := by
  simpa [permutedValues] using congrArg CheckedValues.support permutedValues_eq


theorem permuted_args :
    (obsGraph permutedObs).args = [attI, defI, witI, conI] := by
  simpa [permutedValues] using congrArg CheckedValues.args permutedValues_eq


theorem permuted_edges :
    edges (obsGraph permutedObs) = [(attI, witI), (attI, conI), (defI, attI)] := by
  simpa [permutedValues] using congrArg CheckedValues.edgeList permutedValues_eq


/-! #### Incoming rows, indexed out of the pinned table -/


private theorem minimalArgs : (obsGraph minimalObs).args = [witI, conI] := by
  simpa [minimalValues] using congrArg CheckedValues.args minimalValues_eq


theorem minimal_incoming : incoming (obsGraph minimalObs) witI = [] :=
  incoming_of_rows (i := 0) minimalArgs minimalIncomingRows rfl rfl


private theorem attackedArgs : (obsGraph attackedObs).args = [witI, conI, attI] := by
  simpa [attackedValues] using congrArg CheckedValues.args attackedValues_eq


theorem attacked_incoming : incoming (obsGraph attackedObs) witI = [attI] :=
  incoming_of_rows (i := 0) attackedArgs attackedIncomingRows rfl rfl


theorem attacked_attacker_incoming : incoming (obsGraph attackedObs) attI = [] :=
  incoming_of_rows (i := 2) attackedArgs attackedIncomingRows rfl rfl


private theorem defendedArgs : (obsGraph defendedObs).args = [witI, conI, attI, defI] := by
  simpa [defendedValues] using congrArg CheckedValues.args defendedValues_eq


theorem defended_incoming : incoming (obsGraph defendedObs) witI = [attI] :=
  incoming_of_rows (i := 0) defendedArgs defendedIncomingRows rfl rfl


private theorem selfArgs : (obsGraph selfObs).args = [witI, conI, attI, loopI] := by
  simpa [selfValues] using congrArg CheckedValues.args selfValues_eq


theorem self_incoming : incoming (obsGraph selfObs) witI = [attI] :=
  incoming_of_rows (i := 0) selfArgs selfIncomingRows rfl rfl


theorem self_attacker_incoming : incoming (obsGraph selfObs) attI = [] :=
  incoming_of_rows (i := 2) selfArgs selfIncomingRows rfl rfl


private theorem dischargeBaseArgs : (obsGraph dischargeBaseObs).args = [disI, wrapI] := by
  simpa [dischargeBaseValues] using congrArg CheckedValues.args dischargeBaseValues_eq


theorem dischargeBase_incoming : incoming (obsGraph dischargeBaseObs) wrapI = [] :=
  incoming_of_rows (i := 1) dischargeBaseArgs dischargeBaseIncomingRows rfl rfl


private theorem dischargeAttackArgs : (obsGraph dischargeAttackObs).args = [disI, wrapI, attI] := by
  simpa [dischargeAttackValues] using congrArg CheckedValues.args dischargeAttackValues_eq


theorem dischargeAttack_incoming : incoming (obsGraph dischargeAttackObs) wrapI = [attI] :=
  incoming_of_rows (i := 1) dischargeAttackArgs dischargeAttackIncomingRows rfl rfl


theorem dischargeAttack_attacker_incoming : incoming (obsGraph dischargeAttackObs) attI = [] :=
  incoming_of_rows (i := 2) dischargeAttackArgs dischargeAttackIncomingRows rfl rfl


private theorem filledArgs : (obsGraph filledObs).args = [disI, wrapI] := by
  simpa [filledValues] using congrArg CheckedValues.args filledValues_eq


theorem filled_incoming : incoming (obsGraph filledObs) wrapI = [] :=
  incoming_of_rows (i := 1) filledArgs filledIncomingRows rfl rfl


/-- One attack, two closure edges: the undermined occurrence is shared by the
discharged argument and by the wrapper that discharges it. -/
theorem dischargeAttack_edge_support :
    (attI, wrapI) ∈ edges (obsGraph dischargeAttackObs) := by
  rw [dischargeAttack_edges]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)


/-! ### Grounded status of the queried atom, read off the pinned value -/


theorem minimal_justified :
    statusC (obsGraph minimalObs) (obsClaim minimalObs) = .justified := by
  simpa [minimalValues] using congrArg CheckedValues.status minimalValues_eq


theorem attacked_defeated :
    statusC (obsGraph attackedObs) (obsClaim attackedObs) = .defeated := by
  simpa [attackedValues] using congrArg CheckedValues.status attackedValues_eq


theorem defended_justified :
    statusC (obsGraph defendedObs) (obsClaim defendedObs) = .justified := by
  simpa [defendedValues] using congrArg CheckedValues.status defendedValues_eq


theorem self_defeated :
    statusC (obsGraph selfObs) (obsClaim selfObs) = .defeated := by
  simpa [selfValues] using congrArg CheckedValues.status selfValues_eq


theorem dischargeBase_justified :
    statusC (obsGraph dischargeBaseObs) (obsClaim dischargeBaseObs) = .justified := by
  simpa [dischargeBaseValues] using congrArg CheckedValues.status dischargeBaseValues_eq


theorem dischargeAttack_defeated :
    statusC (obsGraph dischargeAttackObs) (obsClaim dischargeAttackObs) = .defeated := by
  simpa [dischargeAttackValues] using congrArg CheckedValues.status dischargeAttackValues_eq


theorem hole_gap :
    statusC (obsGraph holeObs) (obsClaim holeObs) = .gap := by
  simpa [holeValues] using congrArg CheckedValues.status holeValues_eq


theorem filled_justified :
    statusC (obsGraph filledObs) (obsClaim filledObs) = .justified := by
  simpa [filledValues] using congrArg CheckedValues.status filledValues_eq

/-! ### The comparison record of the first countermodel

These are the facts `LocalityCheck` carries, pinned on the checked material. -/

theorem new_attacker_nodeDiff :
    (obsCheck minimalObs attackedObs).nodeDiff = [attI] := by decide +kernel

theorem new_attacker_edgeDiff :
    (obsCheck minimalObs attackedObs).edgeDiff = [(attI, witI), (attI, conI)] := by decide +kernel

theorem new_attacker_regionBefore :
    (obsCheck minimalObs attackedObs).regionBefore = [witI] := by decide +kernel

theorem new_attacker_regionAfter :
    (obsCheck minimalObs attackedObs).regionAfter = [witI, attI] := by decide +kernel

theorem new_attacker_rejected :
    (obsCheck minimalObs attackedObs).accepted = false := by decide +kernel

theorem node_deletion_rejected :
    (obsCheck defendedObs attackedObs).accepted = false := by decide +kernel

theorem unchanged_despite_failure_rejected :
    (obsCheck minimalObs defendedObs).accepted = false := by decide +kernel

theorem unrelated_self_attack_accepted :
    (obsCheck attackedObs selfObs).accepted = true := by decide +kernel

theorem discharge_propagation_rejected :
    (obsCheck dischargeBaseObs dischargeAttackObs).accepted = false := by decide +kernel

theorem complete_support_from_hole_rejected :
    (obsCheck holeObs filledObs).accepted = false := by decide +kernel

/-! ### The countermodels -/

/-- A new attacker outside the old graph: the test fails and the status moves
`justified` → `defeated`. -/
theorem new_attacker_outside :
    (obsCheck minimalObs attackedObs).accepted = false ∧
    statusC (obsGraph attackedObs) (obsClaim attackedObs) ≠
      statusC (obsGraph minimalObs) (obsClaim minimalObs) :=
  ⟨new_attacker_rejected, by rw [attacked_defeated, minimal_justified]; decide⟩

/-- Deleting the support's defender changes the status and fails correspondence:
the removed node is in the support's own ancestry. -/
theorem node_deletion :
    (obsCheck defendedObs attackedObs).accepted = false ∧
    statusC (obsGraph defendedObs) (obsClaim defendedObs) ≠
      statusC (obsGraph attackedObs) (obsClaim attackedObs) :=
  ⟨node_deletion_rejected, by rw [defended_justified, attacked_defeated]; decide⟩

/-- An attack propagated through the shared discharge subterm: one attack closes
onto both the discharged argument and the query's support, and the status moves
`justified` → `defeated`. -/
theorem discharge_propagation :
    (attI, wrapI) ∈ edges (obsGraph dischargeAttackObs) ∧
    (obsCheck dischargeBaseObs dischargeAttackObs).accepted = false ∧
    statusC (obsGraph dischargeAttackObs) (obsClaim dischargeAttackObs) ≠
      statusC (obsGraph dischargeBaseObs) (obsClaim dischargeBaseObs) :=
  ⟨dischargeAttack_edge_support, discharge_propagation_rejected,
    by rw [dischargeAttack_defeated, dischargeBase_justified]; decide⟩

/-- A hole becoming complete: the support set itself changes, so the test fails
and the status moves `gap` → `justified`. -/
theorem complete_support_from_hole :
    (obsCheck holeObs filledObs).accepted = false ∧
    obsSupport holeObs = [] ∧ obsSupport filledObs = [wrapI] ∧
    statusC (obsGraph holeObs) (obsClaim holeObs) ≠
      statusC (obsGraph filledObs) (obsClaim filledObs) :=
  ⟨complete_support_from_hole_rejected, hole_support, filled_support,
    by rw [hole_gap, filled_justified]; decide⟩

/-- An unrelated self-attack outside every queried ancestor: the test accepts
(node and edge differences are nonempty) and the grounded status is unchanged.
`scope_stable_differs` records that the same edit is not neutral for stable
semantics, which is why the certificate is grounded-only. -/
theorem unrelated_self_attack :
    (obsCheck attackedObs selfObs).accepted = true ∧
    (obsGraph attackedObs).args ≠ (obsGraph selfObs).args ∧
    edges (obsGraph attackedObs) ≠ edges (obsGraph selfObs) ∧
    statusC (obsGraph selfObs) (obsClaim selfObs) =
      statusC (obsGraph attackedObs) (obsClaim attackedObs) :=
  ⟨unrelated_self_attack_accepted,
   by rw [attacked_args, self_args]; decide,
   by rw [attacked_edges, self_edges]; decide,
   by rw [self_defeated, attacked_defeated]⟩

/-- Sufficient-only: changes inside the region cancel. The test fails while both
complete statuses stay `justified`. -/
theorem unchanged_despite_failure :
    (obsCheck minimalObs defendedObs).accepted = false ∧
    statusC (obsGraph defendedObs) (obsClaim defendedObs) =
      statusC (obsGraph minimalObs) (obsClaim minimalObs) :=
  ⟨unchanged_despite_failure_rejected, by rw [defended_justified, minimal_justified]⟩

/-! ### The refuted weaker criteria -/

/-- Comparing the queried supports as raw declaration *names* is not sufficient:
the names agree while the status moves. -/
theorem raw_support_names_insufficient :
    (Coordinates.supports minimalObs.run query).map (·.val) =
      (Coordinates.supports attackedObs.run query).map (·.val) ∧
    statusC (obsGraph attackedObs) (obsClaim attackedObs) ≠
      statusC (obsGraph minimalObs) (obsClaim minimalObs) :=
  ⟨by rw [minimal_supportNames, attacked_supportNames],
   by rw [attacked_defeated, minimal_justified]; decide⟩

/-- Using the *old* ancestry region alone is not sufficient: no changed node and
no changed edge internal to that region, yet a new attacker outside it changes
both the incoming row and the status. -/
theorem old_region_criterion_insufficient :
    oldRegionCriterion (obsGraph minimalObs) (obsGraph attackedObs) (obsSupport minimalObs)
      = true ∧
    (obsCheck minimalObs attackedObs).accepted = false ∧
    statusC (obsGraph attackedObs) (obsClaim attackedObs) ≠
      statusC (obsGraph minimalObs) (obsClaim minimalObs) :=
  ⟨by decide +kernel, new_attacker_rejected,
   by rw [attacked_defeated, minimal_justified]; decide⟩

/-! ### Export, reindexing and pure declaration permutation -/

/-- An alternative carrier containing the same names in another order. -/
def carrierAlt : List Presentation.ArgId := carrier.reverse ++ [⟨"unused"⟩]

theorem minimal_label_reindex :
    labelC (Coordinates.graph minimalObs.run carrier) (carrier.idxOf ⟨"witness"⟩) =
      labelC (Coordinates.graph minimalObs.run carrierAlt) (carrierAlt.idxOf ⟨"witness"⟩) :=
  graph_label_reindex minimalObs.run carrier carrierAlt
    (fun n hn => List.contains_iff_mem.mp (List.all_eq_true.mp (by decide +kernel) n hn))
    (fun n hn => List.contains_iff_mem.mp (List.all_eq_true.mp (by decide +kernel) n hn))
    (by decide +kernel)

/-- The permuted fixture really did shift the checked indices. -/
theorem permuted_indices_shift :
    Coordinates.names permutedObs.run =
      [⟨"attacker"⟩, ⟨"defender"⟩, ⟨"witness"⟩, ⟨"consumer"⟩] := by decide +kernel

/-- Reordering declarations leaves the carrier the same set and preserves every
attack row, so the two lifted graphs are isomorphic under the identity. -/
theorem permuted_iso :
    PW.AFIso (obsGraph permutedObs) (obsGraph defendedObs) id :=
  iso_of_isoCheck (by decide +kernel)

/-- **Pure declaration permutation invariance with the query held fixed**: the
complete status is unchanged. Supports are read at stable identities, never at
the (shifted) checked indices. -/
theorem permuted_status :
    statusC (obsGraph permutedObs) (obsClaim permutedObs) =
      statusC (obsGraph defendedObs) (obsClaim defendedObs) := by
  decide +kernel

/-! ### Scope: grounded only -/

/-- A one-node framework: argument `0` is unattacked. -/
def scopeF : Grounded.AF := ⟨[0], fun _ _ => false⟩

/-- The same framework plus an isolated self-attacking node `1`. -/
def scopeG : Grounded.AF := ⟨[0, 1], fun a b => decide (a = 1 ∧ b = 1)⟩

/-- The grounded label of the pre-existing argument is unchanged. -/
theorem scope_grounded_same : Grounded.labelC scopeF 0 = Grounded.labelC scopeG 0 := by
  rw [labelC_inn_of_incoming_nil (F := scopeF) (a := 0) (by decide) (by decide),
    labelC_inn_of_incoming_nil (F := scopeG) (a := 0) (by decide) (by decide)]

/-- But stable-extension existence is destroyed by the self-attack: no sublist
of `[0, 1]` is stable, while `{0}` is stable in the one-node framework. -/
theorem scope_stable_differs :
    StableCredulous scopeF 0 ∧ ¬ StableCredulous scopeG 0 := by decide

end Lara.Examples.ProcessLocality
