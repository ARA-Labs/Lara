import Lara.Update
import Lara.Examples

namespace Lara.UpdatePreconditionParity

open Lara Lara.Support
open Lara.Presentation (Admission LeafKind Provenance)

private def blankState : Update.SourceState :=
  { sigma := Examples.sigmaEx
  , policy := Examples.unitPolicyEx
  , table := []
  , metas := []
  , leaves := []
  , argsRaw := []
  , rawAtts := []
  , groups := []
  , ground := [] }

private def bit (value : Bool) : String := if value then "1" else "0"

private def row (cells : List String) : String := String.intercalate "\t" cells

private def candidateLeaf : LeafId := ⟨"candidate"⟩

private def leafRows : List String :=
  [false, true].flatMap fun inLeaves =>
    [false, true].flatMap fun inMetas =>
      [false, true].map fun inGroups =>
        let source : Update.SourceState :=
          { blankState with
            leaves := if inLeaves then [(candidateLeaf, Examples.pA)] else []
            metas := if inMetas then
              [{ id := candidateLeaf, kind := .observed, provenance := .user }]
            else []
            groups := if inGroups then
              [{ id := "g", members := [candidateLeaf] }]
            else [] }
        row
          [ "addLeafFreshB"
          , "leaves=" ++ bit inLeaves
          , "metas=" ++ bit inMetas
          , "groups=" ++ bit inGroups
          , toString (Update.addLeafFreshB source candidateLeaf) ]

private def admissionName : Admission → String
  | .admit => "admit"
  | .quarantine => "quarantine"
  | .reject => "reject"

private def decisions : List Admission := [.admit, .quarantine, .reject]

private def admissionTables : List (List Admission) :=
  [[]] ++ decisions.map (fun first => [first]) ++
    decisions.flatMap (fun first => decisions.map (fun second => [first, second]))

private def admissionRows : List String :=
  admissionTables.map fun table =>
    let key : LeafKind × Provenance := (.observed, .user)
    let source : Update.SourceState :=
      { blankState with
        table := table.map fun decision => { key := key, decision := decision } }
    row
      [ "admittedAtB"
      , "table=" ++ if table.isEmpty then "omitted"
          else String.intercalate "," (table.map admissionName)
      , toString (Update.admittedAtB source key) ]

private def attackKinds : List (String × (String → String → RawAttack.RawAttack)) :=
  [ ("rebut", fun source target => .rebut source target)
  , ("undercut", fun source target => .undercut source target [])
  , ("undermine", fun source target => .undermine source target []) ]

private def endpointRows : List String :=
  attackKinds.flatMap fun (kind, makeAttack) =>
    [false, true].flatMap fun sourceDeclared =>
      [false, true].map fun targetDeclared =>
        let sourceName := "source"
        let targetName := "target"
        let source : Update.SourceState :=
          { blankState with
            argsRaw :=
              (if sourceDeclared then [(sourceName, .leaf ⟨"source-term"⟩)] else []) ++
              (if targetDeclared then [(targetName, .leaf ⟨"target-term"⟩)] else []) }
        row
          [ "endpointDeclaredB"
          , "kind=" ++ kind
          , "source=" ++ bit sourceDeclared
          , "target=" ++ bit targetDeclared
          , toString (Update.endpointDeclaredB source (makeAttack sourceName targetName)) ]

private def instanceRows : List String :=
  [false, true].flatMap fun nameCollision =>
    [false, true].map fun termCollision =>
      let candidateName := "candidate"
      let otherName := "other"
      let candidateTerm : SupportTerm := .leaf ⟨"candidate-term"⟩
      let otherTerm : SupportTerm := .leaf ⟨"other-term"⟩
      let source : Update.SourceState :=
        { blankState with
          argsRaw :=
            (if nameCollision then [(candidateName, otherTerm)] else []) ++
            (if termCollision then [(otherName, candidateTerm)] else []) }
      row
        [ "instanceFreshB"
        , "name=" ++ bit nameCollision
        , "term=" ++ bit termCollision
        , toString (Update.instanceFreshB source candidateName candidateTerm) ]

/-! ### In-place discharge and atomic batches -/

private def qOpen : QuestionId := ⟨"q1"⟩
private def qOther : QuestionId := ⟨"q2"⟩

private def openInst : SupportTerm := .inst ⟨"r"⟩ [] [] [] [qOpen] .none
private def closedInst : SupportTerm := .inst ⟨"r"⟩ [] [] [] [] .none
private def wrapInst : SupportTerm :=
  .inst ⟨"w"⟩ [] [openInst] [(qOther, .leaf ⟨"d"⟩)] [] .none

/-- Canonical rendering of the small terms below, shared with the Haskell
emitter: `rule(premises;question=discharge;open)`. -/
private partial def renderTerm : SupportTerm → String
  | .leaf l => l.name
  | .inst r _ ws D H _ =>
      r.name ++ "(" ++ String.intercalate "," (ws.map renderTerm) ++ ";" ++
        String.intercalate "," (D.map fun e => e.1.name ++ "=" ++ renderTerm e.2) ++
        ";" ++ String.intercalate "," (H.map (·.name)) ++ ")"

private def shapes : List (String × SupportTerm) :=
  [("leaf", .leaf ⟨"x"⟩), ("open", openInst), ("closed", closedInst), ("wrap", wrapInst)]

private def positions : List (String × Attack.Pos) :=
  [("eps", []), ("prem0", [.prem 0]), ("prem1", [.prem 1]), ("q2", [.ques qOther])]

private def questions : List (String × QuestionId) := [("q1", qOpen), ("q2", qOther)]

private def dischargeRowsTsv : List String :=
  [false, true].flatMap fun declared =>
    shapes.flatMap fun (shapeName, term) =>
      positions.flatMap fun (posName, pos) =>
        questions.map fun (qName, q) =>
          let source : Update.SourceState :=
            { blankState with
              argsRaw := if declared then [("t", term)] else [] }
          let decided := Update.dischargeOpenB source "t" pos q
          let result :=
            if decided then
              match Update.dischargeRows source.argsRaw "t" pos q (.leaf ⟨"v"⟩) with
              | [(_, rewritten)] => renderTerm rewritten
              | _ => "?"
            else "-"
          row
            [ "dischargeOpenB"
            , "declared=" ++ bit declared
            , "term=" ++ shapeName
            , "pos=" ++ posName
            , "q=" ++ qName
            , toString decided
            , "result=" ++ result ]

private def leafX : LeafId := ⟨"x"⟩
private def leafN : LeafId := ⟨"n"⟩

private def batchBase : Update.SourceState :=
  { blankState with
    leaves := [(leafX, Examples.pA)]
    metas := [{ id := leafX, kind := .observed, provenance := .user }]
    argsRaw := [("a", .leaf leafX), ("h", openInst)] }

private def edits : List (String × Update.AtomicEdit) :=
  [ ("leafNew", .addLeaf leafN Examples.pA
      { id := leafN, kind := .observed, provenance := .user })
  , ("leafOld", .addLeaf leafX Examples.pA
      { id := leafX, kind := .observed, provenance := .user })
  , ("instNew", .addInstance "b" (.leaf leafN))
  , ("instDup", .addInstance "a" (.leaf ⟨"y"⟩))
  , ("attNew", .addAttack (.rebut "b" "a"))
  , ("attOld", .addAttack (.rebut "h" "a"))
  , ("disOk", .dischargeOpen "h" [] qOpen (.leaf leafN))
  , ("disBad", .dischargeOpen "a" [] qOpen (.leaf leafN)) ]

private def renderRejection : Update.UpdateRejection → String
  | .leafNotFresh l => "leafNotFresh " ++ l.name
  | .instanceNotFresh name _ => "instanceNotFresh " ++ name
  | .endpointNotDeclared _ => "endpointNotDeclared"
  | .notDischargeable name _ q => "notDischargeable " ++ name ++ " " ++ q.name
  | .batchEdit index reason => "batchEdit " ++ toString index ++ " " ++
      match reason with
      | .leafNotFresh l => "leafNotFresh " ++ l.name
      | .instanceNotFresh name _ => "instanceNotFresh " ++ name
      | .endpointNotDeclared _ => "endpointNotDeclared"
      | .notDischargeable name _ q => "notDischargeable " ++ name ++ " " ++ q.name
      | _ => "other"
  | _ => "other"

private def renderState (state : Update.SourceState) : String :=
  "args=" ++ String.intercalate ","
      (state.argsRaw.map fun row => row.1 ++ ":" ++ renderTerm row.2) ++
    " atts=" ++ toString state.rawAtts.length ++
    " leaves=" ++ String.intercalate "," (state.leaves.map (·.1.name))

private def batches : List (List (String × Update.AtomicEdit)) :=
  [[]] ++ edits.map (fun e => [e]) ++
    edits.flatMap (fun e => edits.map (fun f => [e, f]))

private def batchRows : List String :=
  batches.map fun batch =>
    let result :=
      match Update.applyBatch batchBase (batch.map (·.2)) with
      | .ok state => "ok " ++ renderState state
      | .error reason => "error " ++ renderRejection reason
    row
      [ "applyBatch"
      , "edits=" ++ (if batch.isEmpty then "none"
          else String.intercalate "," (batch.map (·.1)))
      , result ]

private def rows : List String :=
  leafRows ++ admissionRows ++ endpointRows ++ instanceRows ++
    dischargeRowsTsv ++ batchRows

def emit : IO _root_.Unit := do
  for output in rows do
    IO.println output

end Lara.UpdatePreconditionParity

def main : IO Unit :=
  Lara.UpdatePreconditionParity.emit
