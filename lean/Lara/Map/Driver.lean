/-
# Multi-artifact maps, part 3 — the Lean side of the cross-driver parity anchor

The Lean counterpart of `src/Lara/Map/Driver.hs`, and the map's analogue of
`Lara/Driver.lean`: a decode → **link** → check → encode driver over one
`map-check-input@1` envelope.

## What this driver does and does not read

It **never reads a Haskell verdict.** The envelope carries each member's alias,
its manifest-spelled path, its own declared `artifact` digest, its claim names
paired with their propositions, and its elaborated `unit` — the same
checked-boundary material `Lara.Map.Load` hands to `Lara.Map.Link` — plus the
map's policy id, backend selection, and declared alignments. Everything after
that is recomputed here: qualification, the structural merge, the cross-member
saturation, `Check.Unit.checkUnit`, the grounded labelling, the four-state
statuses, and the alignment assertions. `scripts/check-map-conformance.sh`
byte-compares the resulting `map-verdict@1` bytes and the exit code against
`lara check <map.laramap>`, so an agreement is two implementations reaching one
answer rather than one echoing the other.

It has no `.lara` parser, no `.laramap` parser, and no filesystem story beyond
reading the one file it is given — exactly as `Lara.Driver` has none. Everything
the frontend decides *before* the checked boundary (which files a manifest
names, whether each member checks on its own, whether each member agrees with
the manifest's shared contract, whether a member's admission audit was empty) is
the frontend's, is not recoverable from these bytes, and is not claimed here.

## The units are the members', not the map's

The envelope's `UNIT`s are the members' **own** units, with the members' own
local identifiers. Qualification happens *here*, which is what makes this a
reconstruction: a driver handed a pre-linked unit would only be re-checking
someone else's merge. `Lara.Map.qualifyLeaf` and `Lara.Map.mapLeaf` are the
already-mechanized rename this uses, so the transport results proved in
`Lara/Map/Qualify.lean` are about the function this driver runs.

## Groups are carried by the frontend, not read by either driver

A member's `groups` and duplicate-report mode reach this decoder inside its unit
and are then dropped. Neither map path reads them: `Lara.Map.Link` builds a
`Unit` and hands it to the ordinary `checkUnit`, which reads the signature, the
policy, the arguments and the attacks and nothing else, and this driver does the
same. The §4.3 quarantine that *does* read them belongs to the solo doors — the
Haskell `Lara.Driver.Internal.prune` and this file's sibling
`Lara.Driver.runOnContents` — and a map deliberately does not run it.

What makes that safe is a frontend decision, not one recoverable from these
bytes: `Lara.Map.Load` refuses outright any member whose admission or
group-pruning audit is nonempty. This driver therefore neither re-derives that
refusal nor claims to have.

## Ordering is carried, never imposed

Every section of the verdict is emitted in the order this driver computed it —
members in envelope order, nodes in member-then-declaration order, labels
ascending, edges ascending lexicographic, statuses in member-then-claim order.
Nothing sorts at the printer, for the same reason `Lara.Map.Wire`'s encoder does
not: an ordering bug must be visible in the bytes rather than tidied away.
-/

import Lara.Driver
import Lara.Map.Qualify
import Lara.Context.Fragment

namespace Lara.Map.Driver

open Lara Lara.Support Lara.Attack Lara.RawAttack Lara.Policy
open Lara.Check Lara.Check.Unit
open Lara.Grounded Lara.Compile Lara.Consistency
open Lara.Driver (Sx dcanon printSx parseWire decodeUnit decodeAtom encodeAtom
  buildGamma buildRegistry Decoded termsToList wireRejectionString rejectWire)

/-! ### The closed map keyword vocabulary

Its own table, deliberately disjoint from `Lara.Driver.Tag` as a *type* while
overlapping it on several spellings. The reason is the one the composition
decision record gives for keeping `Lara.Map.Wire.MapTag` out of
`Lara.Wire.Tag`: `Tag` spells the frozen `lara-core@0.2` grammar, is byte-pinned
by conformance goldens, and must not grow a map's vocabulary. This table mirrors
the Haskell side's two map tables — `Lara.Map.Wire.mapTagToString` for the
verdict half and `Lara.Map.Driver.envTagToString` for the envelope half —
which are themselves separate for the same reason one level down. -/

/-- Every keyword of the `map-check-input@1` and `map-verdict@1` grammars. -/
inductive MTag where
  -- the parity envelope
  | mapCheckInput1 | claims | claim
  -- shared between the two grammars
  | policy | backends | backend | members | member | artifact
  | alignments | alignment | ref | whole | arg | same | different
  | author | auditStatus | rationale | unreviewed | reviewed | disputed
  -- the composite verdict
  | mapVerdict1 | scope | map | schema | mapVerdictSchema1 | core
  | nodes | node | labels | edges | statuses | status
  -- grounded labels and four-state statuses
  | inL | outL | undecL
  | gap | justified | contested | defeated
deriving DecidableEq

/-- The on-the-wire spelling of a map keyword — the single source of truth. -/
def mtagToString : MTag → String
  | .mapCheckInput1 => "map-check-input@1"
  | .claims => "claims" | .claim => "claim"
  | .policy => "policy" | .backends => "backends" | .backend => "backend"
  | .members => "members" | .member => "member" | .artifact => "artifact"
  | .alignments => "alignments" | .alignment => "alignment" | .ref => "ref"
  | .whole => "whole" | .arg => "arg"
  | .same => "same" | .different => "different"
  | .author => "author" | .auditStatus => "audit-status"
  | .rationale => "rationale"
  | .unreviewed => "unreviewed" | .reviewed => "reviewed"
  | .disputed => "disputed"
  | .mapVerdict1 => "map-verdict@1"
  | .scope => "scope" | .map => "map"
  | .schema => "schema" | .mapVerdictSchema1 => "lara-map-verdict@1"
  | .core => "core"
  | .nodes => "nodes" | .node => "node" | .labels => "labels"
  | .edges => "edges" | .statuses => "statuses" | .status => "status"
  | .inL => "in" | .outL => "out" | .undecL => "undec"
  | .gap => "gap" | .justified => "justified"
  | .contested => "contested" | .defeated => "defeated"

/-- No two map tags share a spelling. Both Haskell map tables derive their
reverse lookup from their own spelling function by enumerating the type, so a
collision would silently break that inverse; this is the mechanized counterpart
of the two `prop_*TagTableTotal` properties. -/
theorem mtagToString_injective : Function.Injective mtagToString := by
  intro a b
  cases a <;> cases b <;> decide

/-- The core-version spelling the composite verdict carries, mirroring
`Lara.Wire.coreVersionText`. -/
def mapCoreVersionText : String := Lara.Driver.coreVersionText

/-! ### Decode helpers over the shared `Sx` token tree -/

/-- Match `(tag fields*)` and return the fields. -/
def msection (ctx : String) (t : MTag) (e : Sx) : Except String (List Sx) :=
  match e with
  | .list (.atom k :: fs) =>
      if k == mtagToString t then .ok fs
      else .error (ctx ++ ": expected (" ++ mtagToString t ++ " …)")
  | _ => .error (ctx ++ ": expected (" ++ mtagToString t ++ " …)")

/-- Match a tagged list with exactly `arity` payload fields. -/
def mmatch (ctx : String) (t : MTag) (arity : Nat) (e : Sx) :
    Except String (List Sx) := do
  let fs ← msection ctx t e
  if fs.length == arity then .ok fs
  else .error (ctx ++ ": wrong number of fields for " ++ mtagToString t)

def matom (ctx : String) : Sx → Except String String
  | .atom s => .ok s
  | _ => .error (ctx ++ ": expected an atom")

/-- A canonical decimal natural: no sign, no leading zeros, and inside the
Haskell `Int` range its own reprint check bounds. -/
def mnat (ctx : String) (e : Sx) : Except String Nat := do
  let s ← matom ctx e
  match s.toNat? with
  | some n =>
      if toString n == s && n ≤ 0x7fffffffffffffff then .ok n
      else .error (ctx ++ ": malformed natural number: " ++ s)
  | none => .error (ctx ++ ": malformed natural number: " ++ s)

/-- A member alias: nonempty ASCII `[A-Za-z0-9_-]`.

The same restriction `Lara.Map.Types.mkMemberAlias` enforces, and it is load
bearing rather than cosmetic: it is what keeps an alias out of the `:` that
frames a qualified key, so `Lara.Map.qualifyLeaf`'s framing stays unambiguous,
and it keeps every alias inside the bare-atom set so no verdict byte needs
quoting for one. -/
def isAliasChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-'

def malias (ctx : String) (e : Sx) : Except String String := do
  let s ← matom ctx e
  if s != "" && s.all isAliasChar then .ok s
  else .error (ctx ++ ": malformed member alias " ++ s)

/-- The first element that occurs twice, in first-repeat order. -/
def firstDupString : List String → List String → Option String
  | [], _ => none
  | s :: rest, seen => if seen.contains s then some s else firstDupString rest (s :: seen)

/-- Strictly ascending by code-point order on the pair. -/
def backendLt (a b : String × String) : Bool :=
  Lara.Driver.compareCharLists a.1.toList b.1.toList == .lt ||
    (a.1 == b.1 && Lara.Driver.compareCharLists a.2.toList b.2.toList == .lt)

def strictlyAscendingBackends : List (String × String) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => backendLt a b && strictlyAscendingBackends (b :: rest)

/-! ### The decoded envelope

Every identifier below was a bare `String`, which made this mirror *weaker* than
the Haskell it mirrors: confusing a claim name with an alias type-checked here
and not there, and a second implementation that admits confusions the first
rejects is not a second opinion about those confusions.

`Digest` comes from `Lara.Support`, the core's "one newtype per namespace"
module. `MemberAlias`, `ClaimId`, `ArgId`, `PolicyId` and `BackendName` are
defined here rather than imported, and that is deliberate on two counts.
`Lara.Support` has no counterpart for four of them, and its `BackendId` is the
*core's* backend identity, which pairs a name with a numeric version — the
envelope's selection is a name beside a version **string**, exactly as
`Lara.Map.Types` carries it, so reusing the core type would misdescribe the
field. Importing was therefore never an option;
`Lara.Presentation` does define `PropId`, `ArgId` and `PolicyId`, but it is the
*surface* layer and this file is a kernel mirror — importing a presentation type
into the checked boundary would invert the dependency the rest of the
development keeps. `MemberAlias` has no counterpart anywhere, because a map is
the only thing with members. This matches the Haskell side, where
`Lara.Map.Types` owns `MemberAlias`, `ArgIndex` and `NodeIndex` for the same
reason.

`Coord` and `Assertion` are inductives rather than `Option Nat` and `Bool`:
those are boolean blindness at the two places a reader most needs to know which
way round the comparison runs.
-/

/-- A member's alias — the map's own namespace.
Mirrors Haskell's `Lara.Map.Types.MemberAlias`. -/
structure MemberAlias where mk :: (val : String)
deriving DecidableEq

/-- A claim name, as the member's own author wrote it.
Mirrors Haskell's `Lara.AST.PropId` in the position a map uses it. -/
structure ClaimId where mk :: (val : String)
deriving DecidableEq

/-- An argument identifier. Mirrors Haskell's `Lara.AST.ArgId`. -/
structure ArgId where mk :: (val : String)
deriving DecidableEq

/-- The shared contract's policy identifier.
Mirrors Haskell's `Lara.AST.PolicyId`. -/
structure PolicyId where mk :: (val : String)
deriving DecidableEq

/-- A selected backend's name, paired in `MapIn.backends` with its version as a
string. Distinct from `Lara.Support.BackendId`, which is the core's backend
identity and carries a numeric version; this is the envelope's spelling. -/
structure BackendName where mk :: (val : String)
deriving DecidableEq

/-- Which part of a claim's proposition an alignment coordinate selects.
Mirrors Haskell's `Lara.Map.Types.Coord`, and replaces an `Option Nat` in which
`none` silently meant "the whole proposition". -/
inductive Coord where
  | whole : Coord
  | arg : Nat → Coord
deriving DecidableEq

/-- What an alignment asserts about its two coordinates.
Mirrors Haskell's `Lara.Map.Types.Assertion`, and replaces a `Bool` whose
polarity a reader had to recover from the field name. -/
inductive Assertion where
  | same : Assertion
  | different : Assertion
deriving DecidableEq

/-- One alignment coordinate: a member, one of its claims, and which part of
that claim's proposition is meant. -/
structure RefIn where
  memberAlias : MemberAlias
  claim : ClaimId
  coord : Coord
deriving DecidableEq

/-- One declared alignment. The provenance triple the manifest carries is
decoded for well-formedness and then dropped: who asserted a thing and whether
a reviewer looked at it decide nothing about whether it holds. -/
structure AlignmentIn where
  left : RefIn
  right : RefIn
  assertion : Assertion

/-- One member at the checked boundary. -/
structure MemberIn where
  memberAlias : MemberAlias
  path : String
  artifact : Digest
  claims : List (ClaimId × Atom)
  decoded : Decoded

/-- A whole map at its checked boundary. -/
structure MapIn where
  policy : PolicyId
  backends : List (BackendName × String)
  members : List MemberIn
  alignments : List AlignmentIn

def decodeCoordIn (ctx : String) (e : Sx) : Except String Coord :=
  match e with
  | .atom s => if s == mtagToString .whole then .ok .whole
               else .error (ctx ++ ": expected whole or (arg NAT)")
  | .list _ => do
      let fs ← mmatch ctx .arg 1 e
      match fs with
      | [n] => (mnat ctx n).map .arg
      | _ => .error (ctx ++ ": expected whole or (arg NAT)")

def decodeRefIn (e : Sx) : Except String RefIn := do
  let fs ← mmatch ctx .ref 3 e
  match fs with
  | [a, c, coord] => do
      let memberAlias ← malias ctx a
      let claim ← matom ctx c
      let coordValue ← decodeCoordIn ctx coord
      .ok { memberAlias := ⟨memberAlias⟩, claim := ⟨claim⟩, coord := coordValue }
  | _ => .error (ctx ++ ": malformed ref")
where ctx := "map check-input ref"

/-- Whether two coordinates select the same *kind* of target. A pair mixing a
whole-claim selector with an argument selector is not a comparison anyone can
state, and is refused rather than interpreted. -/
def sameSelectorKind : Coord → Coord → Bool
  | .whole, .whole => true
  | .arg _, .arg _ => true
  | _, _ => false

def decodeAlignmentIn (e : Sx) : Except String AlignmentIn := do
  let fs ← mmatch ctx .alignment 6 e
  match fs with
  | [l, r, assertion, authorS, auditS, rationaleS] => do
      let left ← decodeRefIn l
      let right ← decodeRefIn r
      let assertText ← matom ctx assertion
      let assertionValue ←
        if assertText == mtagToString .same then (.ok .same : Except String Assertion)
        else if assertText == mtagToString .different then .ok .different
        else .error (ctx ++ ": expected same|different")
      -- The provenance triple: checked for shape, then dropped.
      let authorFs ← mmatch ctx .author 1 authorS
      let _ ← authorFs.mapM (matom ctx)
      let auditFs ← mmatch ctx .auditStatus 1 auditS
      let auditText ← (match auditFs with
        | [a] => matom ctx a
        | _ => .error (ctx ++ ": malformed audit-status"))
      let _ ←
        if auditText == mtagToString .unreviewed || auditText == mtagToString .reviewed
            || auditText == mtagToString .disputed then
          (.ok () : Except String _root_.Unit)
        else .error (ctx ++ ": expected unreviewed|reviewed|disputed")
      let rationaleFs ← mmatch ctx .rationale 1 rationaleS
      let _ ← rationaleFs.mapM (matom ctx)
      if sameSelectorKind left.coord right.coord then
        .ok { left := left, right := right, assertion := assertionValue }
      else
        .error (ctx ++ ": an alignment's two coordinates must both be whole or both be (arg n)")
  | _ => .error (ctx ++ ": malformed alignment")
where ctx := "map check-input alignment"

/-- A member's claim names paired with their propositions, in declaration
order. The names must be unique within the member: `(alias, claim name)` is the
map's reporting handle, and resolution of an alignment coordinate is a
first-wins lookup, so a repeat would silently give one status two meanings. -/
def decodeClaimsIn (memberAlias : String) (e : Sx) : Except String (List (ClaimId × Atom)) := do
  let ctx := "map check-input claims of member " ++ memberAlias
  let fs ← msection ctx .claims e
  let claims ← fs.mapM (fun f => do
    let cf ← mmatch ctx .claim 2 f
    match cf with
    | [name, atomS] => do
        let n ← matom ctx name
        let p ← decodeAtom atomS
        .ok ((⟨n⟩ : ClaimId), p)
    | _ => .error (ctx ++ ": malformed claim"))
  match firstDupString (claims.map (·.1.val)) [] with
  | some dup => .error (ctx ++ ": duplicate claim name " ++ dup)
  | none => .ok claims

def decodeMemberIn (e : Sx) : Except String MemberIn := do
  let ctx := "map check-input member"
  let fs ← mmatch ctx .member 5 e
  match fs with
  | [aliasS, pathS, artifactS, claimsS, unitS] => do
      let memberAlias ← malias ctx aliasS
      -- Nonempty, mirroring `Lara.Map.Types.mkDeclaredPath` on the Haskell
      -- side. Without this the two decoders would not accept the same
      -- language: an envelope carrying `(member paper_pos "" …)` would be
      -- refused there and produce a full verdict here, which is precisely the
      -- kind of divergence the parity harness exists to make impossible.
      let path ← matom ctx pathS
      let _ ←
        if path.isEmpty then
          (.error (ctx ++ ": path must be a nonempty atom") : Except String _root_.Unit)
        else .ok ()
      let artifactFs ← mmatch ctx .artifact 1 artifactS
      let artifact ← (match artifactFs with
        | [d] => matom ctx d
        | _ => .error (ctx ++ ": malformed artifact"))
      let claims ← decodeClaimsIn memberAlias claimsS
      let decoded ← decodeUnit unitS
      -- `decodeUnit` scans a unit's argument ids and its groups for repeats and
      -- NOT its leaves, and neither does the Haskell wire decoder, so a
      -- repeated leaf id survives to here. It has to be refused: `buildGamma`
      -- is first-wins, so one leaf would shadow the other and every argument
      -- built on the shadowed one would be checked against a proposition its
      -- author never wrote. Decided per member, while there is still a member
      -- to name.
      let _ ← (match firstDupString (decoded.leaves.map (·.1.name)) [] with
        | some dup =>
            (.error (ctx ++ " " ++ memberAlias ++ ": duplicate leaf id " ++ dup)
              : Except String _root_.Unit)
        | none => .ok ())
      .ok { memberAlias := ⟨memberAlias⟩, path := path, artifact := ⟨artifact⟩
          , claims := claims, decoded := decoded }
  | _ => .error (ctx ++ ": malformed member")

/-- Every member's unit agrees with the first on the sections that come from the
**shared policy** rather than from the member's own text.

On the `.laramap` door this is a consequence rather than a check: the frontend
compares every member against the *manifest's* policy, so members that get that
far agree with each other by transitivity. An envelope has no manifest policy
file behind it and no loader — its bytes are all a reader has — so the
consequence has to become the check here. Without it a hand-written envelope
could link two members that never ran under one policy, and the composite
verdict would be a statement about a corpus nobody wrote. -/
def sharedSectionsAgree : List MemberIn → Except String _root_.Unit
  | [] => .ok ()
  | first :: rest =>
      rest.forM (fun m =>
        let ctx := "map check-input members: members " ++ first.memberAlias.val
          ++ " and " ++ m.memberAlias.val ++ " disagree on the shared policy's "
        if m.decoded.sigma != first.decoded.sigma then
          (.error (ctx ++ "signature") : Except String _root_.Unit)
        else if m.decoded.policy != first.decoded.policy then
          .error (ctx ++ "rules, contraries or exceptions")
        else if m.decoded.theories != first.decoded.theories then
          .error (ctx ++ "theories")
        else if m.decoded.groupMode != first.decoded.groupMode then
          .error (ctx ++ "duplicate-report mode")
        else .ok ())

/-- The argument list of a claim's proposition. -/
def claimArgs : Atom → List Term
  | .atom _ ts => termsToList ts

/-- Every alignment coordinate names a declared member, a claim that member
declares, and an argument position that claim has.

The same three conditions `Lara.Map.Driver.resolveRef` decides on the `.laramap`
door, made a property of the envelope's own bytes because a driver reading this
form has no manifest to resolve against. -/
def resolvableRef (members : List MemberIn) (r : RefIn) : Except String Atom := do
  let ctx := "map check-input alignment"
  match members.find? (fun m => m.memberAlias == r.memberAlias) with
  | none => .error (ctx ++ ": undeclared member alias " ++ r.memberAlias.val)
  | some m =>
    match m.claims.find? (fun c => c.1 == r.claim) with
    | none =>
        .error (ctx ++ ": member " ++ r.memberAlias.val
          ++ " declares no claim " ++ r.claim.val)
    | some c =>
      match r.coord with
      | .whole => .ok c.2
      | .arg i =>
          if i < (claimArgs c.2).length then .ok c.2
          else .error (ctx ++ ": claim " ++ r.claim.val ++ " of member "
            ++ r.memberAlias.val ++ " has no argument " ++ toString i)

def decodeMapInput (e : Sx) : Except String MapIn := do
  let ctx := "map check-input"
  let fs ← mmatch ctx .mapCheckInput1 4 e
  match fs with
  | [policyS, backendsS, membersS, alignmentsS] => do
      let policyFs ← mmatch (ctx ++ " policy") .policy 1 policyS
      let policy ← (match policyFs with
        | [p] => matom (ctx ++ " policy") p
        | _ => .error (ctx ++ " policy: malformed policy"))
      let backendFs ← msection (ctx ++ " backends") .backends backendsS
      let backends ← backendFs.mapM (fun f => do
        let bf ← mmatch (ctx ++ " backends") .backend 2 f
        match bf with
        | [n, v] => do
            let name ← matom (ctx ++ " backends") n
            let version ← matom (ctx ++ " backends") v
            .ok ((⟨name⟩ : BackendName), version)
        | _ => .error (ctx ++ " backends: malformed backend"))
      let _ ←
        if strictlyAscendingBackends (backends.map (fun b => (b.1.val, b.2))) then
          (.ok () : Except String _root_.Unit)
        else .error (ctx ++ " backends: backends must be duplicate-free and ascending by (id, version)")
      let memberFs ← msection (ctx ++ " members") .members membersS
      let members ← memberFs.mapM decodeMemberIn
      let _ ←
        if members.isEmpty then
          (.error (ctx ++ " members: a map check-input declares at least one member")
            : Except String _root_.Unit)
        else .ok ()
      let _ ← (match firstDupString (members.map (·.memberAlias.val)) [] with
        | some dup => (.error (ctx ++ " members: duplicate member alias " ++ dup)
            : Except String _root_.Unit)
        | none => .ok ())
      let _ ← sharedSectionsAgree members
      let alignFs ← msection (ctx ++ " alignments") .alignments alignmentsS
      let alignments ← alignFs.mapM decodeAlignmentIn
      let _ ← alignments.forM (fun a => do
        let _ ← resolvableRef members a.left
        let _ ← resolvableRef members a.right
        pure ())
      .ok { policy := ⟨policy⟩, backends := backends, members := members
          , alignments := alignments }
  | _ => .error (ctx ++ ": malformed map check input")

/-! ### Qualification and the merge

The Haskell mirror is `Lara.Map.Qualify.qualifyMember` and
`Lara.Map.Link.mergeArguments`. What is qualified is *handles* — leaf
identifiers and every reference to them inside a support term or an attack — and
what is not is *meanings*: propositions, rule ids, discharge keys, certificate
premise positions and theory digests are shared across the map and renaming one
would make a member's material unreadable against the policy the map checks
under.

Argument identifiers do not need renaming on this side: an `Attack` here already
carries **terms** at its endpoints (`Lara.RawAttack.resolveAttacks` resolved them
at the member's own decode), so a merged argument *is* its term and there is no
second identity to re-point. The Haskell side re-points argument ids because its
`Attack` is id-carrying and its checker resolves ids later; the two arrive at the
same resolved graph. What this driver does carry is each member's **local**
argument id, unrenamed, because the verdict's `nodes` section reports it. -/

/-- One member's material with every local leaf identity renamed into the map's
namespace. -/
structure QualifiedMember where
  memberAlias : MemberAlias
  leaves : List (LeafId × Atom)
  /-- `(local argument id, qualified term)`, in the member's declaration order. -/
  args : List (ArgId × SupportTerm)
  atts : List Attack
  queries : List Atom

def qualifyMemberIn (m : MemberIn) : QualifiedMember :=
  let a := m.memberAlias.val
  { memberAlias := m.memberAlias
  , leaves := Lara.Map.qualifyGamma a m.decoded.leaves
  , args := m.decoded.argsRaw.map
      (fun p => ((⟨p.1⟩ : ArgId), Lara.Map.mapLeaf (Lara.Map.qualifyLeaf a) p.2))
  , atts := m.decoded.atts.map (Lara.Map.mapLeafAtt (Lara.Map.qualifyLeaf a))
  , queries := m.decoded.queries }

/-- Keep the first occurrence of each element. -/
def dedupAtoms : List Atom → List Atom → List Atom
  | [], _ => []
  | p :: rest, seen => if seen.contains p then dedupAtoms rest seen else p :: dedupAtoms rest (p :: seen)

def dedupStrings : List String → List String → List String
  | [], _ => []
  | s :: rest, seen => if seen.contains s then dedupStrings rest seen else s :: dedupStrings rest (s :: seen)

def dedupAttacks : List Attack → List Attack → List Attack
  | [], _ => []
  | k :: rest, seen => if seen.contains k then dedupAttacks rest seen else k :: dedupAttacks rest (k :: seen)

/-- The distinct terms, in first-declaration order. -/
def firstOccurrences : List SupportTerm → List SupportTerm → List SupportTerm
  | [], _ => []
  | w :: rest, seen =>
      if seen.contains w then firstOccurrences rest seen
      else w :: firstOccurrences rest (w :: seen)

/-- Every `(member alias, local argument id, qualified term)` any member
declared, in member order and then that member's own declaration order. -/
def declaredArgs (ms : List QualifiedMember) :
    List (MemberAlias × ArgId × SupportTerm) :=
  ms.flatMap (fun m => m.args.map (fun p => (m.memberAlias, p.1, p.2)))

/-- The members that declared a given linked term, in member order and
duplicate-free. Nonempty by construction: a linked argument exists because some
member declared its term. -/
def ownersOf (declared : List (MemberAlias × ArgId × SupportTerm)) (w : SupportTerm) :
    List String :=
  dedupStrings (declared.filterMap (fun d => if d.2.2 == w then some d.1.val else none)) []

/-- Two linked arguments are a cross-member pair when some member declared the
one and a **different** member declared the other. With the structural merge
inactive — which it is under every policy this repository ships, because leaf
qualification confines a term collision to a single member — each owner list is
a singleton and this is alias inequality. -/
def crossMember (sources targets : List String) : Bool :=
  sources.any (fun s => targets.any (fun t => s != t))

/-! ### The linked map -/

/-- One `(member alias, local argument id)` handle and the linked index it
resolved to. -/
structure NodeOut where
  memberAlias : MemberAlias
  argId : ArgId
  index : Nat

/-- One map-relative claim status. -/
structure StatusOut where
  memberAlias : MemberAlias
  claim : ClaimId
  atom : Atom
  status : Status

/-- The checked, evaluated map: everything the composite verdict reports. -/
structure LinkedOut where
  nodes : List NodeOut
  labels : List (Nat × Label)
  edges : List (Nat × Nat)
  statuses : List StatusOut

/-- Why a map was refused after its bytes decoded.

Three constructors, and they are the map's exit-1 causes that survive the
checked boundary: a structural link failure, the linked unit not checking, and a
declared alignment not holding. Everything else the Haskell `MapError` sum can
say is about files, manifests and members — decisions taken before this envelope
existed.

`linkBoundary` mirrors Haskell's `MRLinkBoundary`, and it is here because
without it the two link-stage failures below returned `Except String` and exited
`2` where their Haskell counterparts are map rejections at `1`. Both are
unreachable — the decoder refuses an envelope with no members, and refuses a
repeated qualified leaf — so no verdict byte moves either way. The point is that
the harness compares exit codes, and a claim of the form "the codes mirror
exactly" should be true rather than true-on-reachable-inputs. -/
inductive MapReject where
  | linkBoundary : String → MapReject
  | linkRejected : Lara.Driver.WireRejection → MapReject
  | alignmentFalse : Nat → Bool → MapReject

/-- The `stderr` line for a refusal. The text after the driver's own name
mirrors `Lara.Map.Types.renderMapError` word for word, so the two drivers'
diagnostics differ only in the prefix that names which one spoke. -/
def rejectMessage : MapReject → String
  | .linkBoundary message => "map link boundary: " ++ message
  | .linkRejected cls => "map link rejected: " ++ wireRejectionString cls
  | .alignmentFalse position assertSame =>
      "map alignment " ++ toString position
        ++ ": the two coordinates are asserted to be "
        ++ (if assertSame then "identical" else "distinct")
        ++ ", and they are not"

/-! ### Alignment evaluation

An alignment is a claim *about* the members, decided against them; it is never a
rewrite that makes them agree. Identity is `≡` on both arms — `Lara.nf` for a
whole proposition and `Lara.nfTerm` for one argument position — because that is
the trusted identity relation the checker itself uses, and comparing raw syntax
instead would make an alignment turn on a numeric literal's spelling. -/

/-- The value one coordinate names, or `none` when it does not resolve. The
decoder has already refused an envelope in which one does not, so the `none`
arms are unreachable from `main`; they are written out rather than defaulted
because a defaulted value would silently decide an assertion. -/
def selectAt (members : List MemberIn) (r : RefIn) : Option (Sum Atom Term) := do
  let m ← members.find? (fun m => m.memberAlias == r.memberAlias)
  let c ← m.claims.find? (fun c => c.1 == r.claim)
  match r.coord with
  | .whole => some (.inl c.2)
  | .arg i => ((claimArgs c.2)[i]?).map .inr

def coordsIdentical : Sum Atom Term → Sum Atom Term → Bool
  | .inl p, .inl q => Lara.nf dcanon p == Lara.nf dcanon q
  | .inr s, .inr t => Lara.nfTerm dcanon s == Lara.nfTerm dcanon t
  | _, _ => false

/-- The lowest-numbered alignment that does not hold, if any. -/
def firstFalseAlignment (members : List MemberIn) :
    List AlignmentIn → Nat → Option MapReject
  | [], _ => none
  | a :: rest, position =>
      let verdict :=
        match selectAt members a.left, selectAt members a.right with
        | some l, some r =>
            let identical := coordsIdentical l r
            match a.assertion with
            | .same => identical
            | .different => !identical
        | _, _ => false
      if verdict then firstFalseAlignment members rest (position + 1)
      else some (.alignmentFalse position (a.assertion == .same))

/-! ### Verdict encoders (mirror `Lara.Map.Wire.encodeMapVerdict`) -/

def sxNat (n : Nat) : Sx := .atom (toString n)

def labelStr : Label → String
  | .inn => mtagToString .inL
  | .out => mtagToString .outL
  | .undec => mtagToString .undecL

def statusStr : Status → String
  | .gap => mtagToString .gap
  | .justified => mtagToString .justified
  | .contested => mtagToString .contested
  | .defeated => mtagToString .defeated

/-- The composite verdict. Every section prints in the order the driver computed
it; nothing is sorted here. -/
def encodeMapVerdict (input : MapIn) (linked : LinkedOut) : Sx :=
  .list
    [ .atom (mtagToString .mapVerdict1)
    , .list [.atom (mtagToString .scope), .atom (mtagToString .map)]
    , .list [.atom (mtagToString .schema), .atom (mtagToString .mapVerdictSchema1)]
    , .list [.atom (mtagToString .core), .atom mapCoreVersionText]
    , .list [.atom (mtagToString .policy), .atom input.policy.val]
    , .list (.atom (mtagToString .backends) ::
        input.backends.map (fun bv =>
          .list [.atom (mtagToString .backend), .atom bv.1.val, .atom bv.2]))
    , .list (.atom (mtagToString .members) ::
        input.members.map (fun m =>
          .list [ .atom (mtagToString .member), .atom m.memberAlias.val, .atom m.path
                , .list [.atom (mtagToString .artifact), .atom m.artifact.hash]]))
    , .list (.atom (mtagToString .nodes) ::
        linked.nodes.map (fun n =>
          .list [ .atom (mtagToString .node), .atom n.memberAlias.val
                , .atom n.argId.val, sxNat n.index]))
    , .list (.atom (mtagToString .labels) ::
        linked.labels.map (fun le => .list [sxNat le.1, .atom (labelStr le.2)]))
    , .list (.atom (mtagToString .edges) ::
        linked.edges.map (fun ij => .list [sxNat ij.1, sxNat ij.2]))
    , .list (.atom (mtagToString .statuses) ::
        linked.statuses.map (fun s =>
          .list [ .atom (mtagToString .status), .atom s.memberAlias.val
                , .atom s.claim.val, encodeAtom s.atom
                , .atom (statusStr s.status)]))
    ]

/-! ### The driver -/

/-- Link, check and evaluate a decoded envelope.

The stages are `Lara.Map.Link.linkMap`'s, in its order: qualify every member,
concatenate the qualified leaf contexts, merge the arguments structurally,
transport the members' own attacks, generate the cross-member conflict attacks,
run the **ordinary** `checkUnit` on the result, and read the grounded result off
the accepted unit — then, as `Lara.Map.Driver.checkMap`'s next stage, decide the
declared alignments. Nothing is asserted: the linked unit is an ordinary unit
and goes through the ordinary checker, so this driver cannot accept anything a
hand-written equivalent unit would not.

The duplicate-leaf guard here is defensive and cannot fire, which is a change
from how it started: `decodeMemberIn` now refuses a member whose own leaf ids
repeat, and two *different* members cannot collide because aliases are unique by
decode and `Lara.Map.qualifiedKey` is injective (`qualifiedKey_inj`). Between
them those two facts cover every case.

It is kept rather than deleted because what it protects is silent.
`buildGamma` is first-wins, so a collision that did get through would let one
leaf shadow another and every argument built on the shadowed one would be
checked against a proposition its author never wrote — no error anywhere, just a
verdict about a program nobody wrote. Its message names the qualified key, since
by construction that is the only thing it could have found. -/
def linkAndEvaluate (input : MapIn) : Except String (Except MapReject LinkedOut) := do
  -- The empty arm cannot be reached: `decodeMapInput` refuses an envelope with
  -- no members. It is matched rather than defaulted because the alternative is
  -- a partial pattern, and because a defaulted "shared contract" would be one
  -- no member ever agreed to.
  --
  -- Both this and the duplicate-leaf arm below return a `MapReject` rather than
  -- an `Except String`, so each exits `1` beside its Haskell counterpart
  -- (`MRLinkBoundary`) instead of `2`. Neither is reachable, so this moves no
  -- verdict byte; what it fixes is that the harness compares exit codes and the
  -- docstring on `runOnContents` claims they mirror exactly.
  match input.members with
  | [] => .ok (.error (.linkBoundary "a map declares no members"))
  | firstMember :: _ =>
  let shared := firstMember.decoded
  let qualified := input.members.map qualifyMemberIn
  let leaves := qualified.flatMap (·.leaves)
  match firstDupString (leaves.map (·.1.name)) [] with
  | some dup =>
      .ok (.error (.linkBoundary ("two members declare the leaf identity " ++ dup)))
  | none => do
  let declared := declaredArgs qualified
  let linkedTerms := firstOccurrences (declared.map (·.2.2)) []
  -- One node per declared `(member alias, local argument id)`, naming the linked
  -- position its term became. `findIdx?` never misses: `linkedTerms` is the
  -- distinct terms of this very list, so every declared term either is a first
  -- occurrence or equals an earlier one. `filterMap` is the total spelling of
  -- that, and dropping a handle rather than inventing an index is the safe way
  -- for it to be wrong, because a fabricated index would put a node in a
  -- verdict that names an argument nobody declared.
  let nodes : List NodeOut :=
    declared.filterMap (fun d =>
      (linkedTerms.findIdx? (fun w => w == d.2.2)).map (fun i =>
        { memberAlias := d.1, argId := d.2.1, index := i }))
  let gamma := buildGamma leaves
  let reg := buildRegistry shared.theories
  let pI := shared.policy.ruleLookup
  let dp := shared.policy.defeat
  -- The conclusions of the linked arguments that are complete checked support.
  -- A term that fails to infer, or retains an open critical-question
  -- obligation, contributes none: `checkUnit` runs afterwards and rejects the
  -- linked unit for exactly those terms, so skipping them here only avoids
  -- emitting an attack whose endpoint the checker is about to refuse.
  let cache : List (Nat × SupportTerm × Atom) :=
    (linkedTerms.zipIdx).filterMap (fun p =>
      (Lara.Context.conclusionOf pI gamma reg p.1).map (fun c => (p.2, p.1, c)))
  let generated : List Attack :=
    cache.flatMap (fun s =>
      cache.filterMap (fun t =>
        if crossMember (ownersOf declared s.2.1) (ownersOf declared t.2.1)
            && contraryMatchB dcanon dp s.2.2 t.2.2
            && conflictAttackableB pI t.2.1 then
          some (Lara.Context.attackFor s.2.1 t.2.1)
        else none))
  let transported := qualified.flatMap (·.atts)
  let queries := dedupAtoms (qualified.flatMap (·.queries)) []
  let ground := leaves.map (·.2) ++ shared.theories.flatMap (·.2) ++ queries
  let unit : Lara.Unit :=
    { sigma := shared.sigma
    , policy := shared.policy
    , args := linkedTerms
    , atts := dedupAttacks (transported ++ generated) [] }
  match checkUnit gamma reg ground unit with
  | .error err => .ok (.error (.linkRejected (rejectWire err)))
  | .ok accepted =>
    let af := checkedAF accepted.program
    let n := accepted.program.args.length
    let labels := (List.range n).map (fun i => (i, labelC af i))
    let edges := (List.range n).foldr
      (fun i acc => (List.range n).foldr
        (fun j acc2 => if af.attack i j then (i, j) :: acc2 else acc2) acc) []
    let statuses : List StatusOut :=
      input.members.flatMap (fun m =>
        m.claims.map (fun c =>
          { memberAlias := m.memberAlias, claim := c.1, atom := c.2
          , status := statusC af (completeClaimFor accepted c.2) }))
    -- The alignments are decided AFTER the grounded result, not before, so the
    -- stage order matches `Lara.Map.Driver.checkMap`'s exactly: link, evaluate,
    -- then decide the alignments. Failing earlier would be observationally the
    -- same — a refused map prints no verdict either way — and the two mirrors
    -- would then differ in code for no reason a reader could check.
    match firstFalseAlignment input.members input.alignments 0 with
    | some failure => .ok (.error failure)
    | none =>
        .ok (.ok { nodes := nodes, labels := labels, edges := edges, statuses := statuses })

/-- Exit codes mirror the Haskell map door exactly: `0` with the composite
verdict on `stdout`, `1` for a map that was understood and refused, `2` for a
map that could not be read or decoded. A refusal prints nothing on `stdout`.

"Exactly" is meant literally, and it was not always true: the two link-stage
structural failures used to leave `linkAndEvaluate` as an `Except String` and
exit `2`, where their Haskell counterparts are `MRLinkBoundary` map rejections at
`1`. Both are unreachable — the decoder refuses an envelope with no members, and
refuses a repeated qualified leaf — so the divergence moved no verdict byte and
no committed fixture. It is fixed rather than documented because
`scripts/check-map-conformance.sh` compares exit codes, and a mirror claim the
harness relies on should hold on every input rather than on every reachable
one. -/
def runOnContents (contents : String) : IO _root_.Unit := do
  match parseWire contents with
  | .error msg =>
      IO.eprintln ("lara-map-driver: map codec error at " ++ msg)
      IO.Process.exit 2
  | .ok e =>
    match decodeMapInput e with
    | .error msg =>
        IO.eprintln ("lara-map-driver: map codec: " ++ msg)
        IO.Process.exit 2
    | .ok input =>
      match linkAndEvaluate input with
      | .error msg =>
          IO.eprintln ("lara-map-driver: " ++ msg)
          IO.Process.exit 2
      | .ok outcome =>
        match outcome with
        | .error failure =>
            IO.eprintln ("lara-map-driver: " ++ rejectMessage failure)
            IO.Process.exit 1
        | .ok linked =>
            IO.println (printSx (encodeMapVerdict input linked))

/-- Executable entry point: `lara-map-driver <file.sexp>`. -/
def main (args : List String) : IO _root_.Unit := do
  match args with
  | [path] => do
      let contents ← (do
        try
          IO.FS.readFile (⟨path⟩ : System.FilePath)
        catch _ =>
          IO.eprintln ("lara-map-driver: cannot read " ++ path)
          IO.Process.exit 2)
      runOnContents contents
  | _ =>
      IO.eprintln "usage: lara-map-driver <file.sexp>"
      IO.Process.exit 2

end Lara.Map.Driver
