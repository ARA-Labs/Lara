/- Checked registry fixtures use a genuine nonidentity p/q → P/Q bridge. -/
import Lara.PW.Declared
import Lara.Examples.PWSurface

namespace Lara.Examples.PWDeclared
open Lara.PW Lara.PW.Surface Lara.PW.Surface.Declared
open Lara.Examples.PWSurface

def contextName : Bool → CtxId
  | false => ⟨"src"⟩
  | true => ⟨"tgt"⟩

def contextOf (n : CtxId) : Option Bool :=
  if n = ⟨"src"⟩ then some false else if n = ⟨"tgt"⟩ then some true else none

def host : Host where
  K := Bool
  ctx := fun k => if k then ctxTgt else ctxSrc
  ctxName := contextName
  ctxOf := contextOf
  ctxOf_ctxName := by intro k; cases k <;> decide
  ctxName_of_ctxOf := by
    intro n k h
    unfold contextOf at h
    split at h
    · rename_i hn
      cases h
      exact hn.symm
    · split at h
      · rename_i hn
        cases h
        exact hn.symm
      · cases h
  canon_shared := by intro k l; cases k <;> cases l <;> rfl

def checked : Resolved host :=
  ⟨declOK, false, true, ⟨symMapOf declSymbols, leafMapOf declLeaves⟩,
    elaborates_declOK⟩

def registry : Registry host := ⟨[checked]⟩

theorem loaded : load host [declOK] = .ok registry := by rfl

def error? {α : Type} : Except LoadError α → Option LoadError
  | .ok _ => none
  | .error e => some e

theorem duplicate_rejected :
    error? (load host [declOK, declOK]) = some (.duplicateBridge ⟨"b"⟩) := by decide

theorem unknown_source_rejected :
    error? (load host [declOtherSource]) =
      some (.unknownSource ⟨"b"⟩ ⟨"elsewhere"⟩) := by decide

theorem unknown_target_rejected :
    error? (load host [declOtherTarget]) =
      some (.unknownTarget ⟨"b"⟩ ⟨"elsewhere"⟩) := by decide

theorem clause_rejected :
    error? (load host [declMissingClause]) =
      some (.invalidBridge ⟨"b"⟩ (.missingClause .ruleOk)) := by decide

/-- Every clause is listed, but the map drops `q`, so the source rule no longer
translates and T6's rule clause fails during loading. -/
def declUntranslatable : BridgeDecl := { declOK with symbols := declSymbolsNoQ }

theorem rule_rejected :
    error? (load host [declUntranslatable]) =
      some (.invalidBridge ⟨"b"⟩ .ruleClauseFails) := by decide

def relation (r : Resolved host) :
    Instance.World (host.ctx r.source) → Instance.World (host.ctx r.target) → Prop :=
  fun _ _ => True

def bridge : registry.B := ⟨⟨"b"⟩, by decide⟩

theorem name_resolves :
    (registry.naming relation relation).bridgeOf ⟨"b"⟩ = some bridge := rfl

/-- The query's bridge map genuinely renames; it is not the old identity map. -/
theorem declared_translation :
    ((registry.data relation relation).sym bridge).predMap "q" = some "Q" := by decide

theorem undeclared_rejected :
    formError? (elabForm (registry.naming relation relation) false
      (.dia ⟨"missing"⟩ .top)) = some (.unknownBridge ⟨"missing"⟩) := by decide

theorem context_mismatch_rejected :
    formError? (elabForm (registry.naming relation relation) true
      (.dia ⟨"b"⟩ .top)) =
      some (.bridgeSourceMismatch ⟨"b"⟩ ⟨"tgt"⟩ ⟨"src"⟩) := by decide

/-- Both modalities remain linked below conjunction and negation. -/
def nested : SForm :=
  .conj (.dia ⟨"b"⟩ .top) (.neg (.box ⟨"b"⟩ .top))

theorem nested_elaborates :
    formError? (elabForm (registry.naming relation relation) false nested) = none := by decide

/-- No status atom is silently translated while typing a modal operand. The
source spelling q is not a predicate of the target's P/Q signature. -/
theorem source_spelling_rejected :
    (formError? (elabForm (registry.naming relation relation) false
      (.dia ⟨"b"⟩ (.status .justified (.atom "q" .nil))))).isSome = true := by decide

end Lara.Examples.PWDeclared
