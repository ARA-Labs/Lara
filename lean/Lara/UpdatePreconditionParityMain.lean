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

private def rows : List String :=
  leafRows ++ admissionRows ++ endpointRows ++ instanceRows

def emit : IO _root_.Unit := do
  for output in rows do
    IO.println output

end Lara.UpdatePreconditionParity

def main : IO Unit :=
  Lara.UpdatePreconditionParity.emit
