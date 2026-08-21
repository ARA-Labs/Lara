/-
Mechanized codec round-trip for the LARA **presentation AST** (spec §9 result 12).

This module models the complete live presentation `Program`/`Policy` shape of
`src/Lara/AST.hs` at `lara-syntax@0.8` — every field of both top-levels,
including inferred argument instantiations and the `lara-core@0.2` `policySigma`,
below — defines a **structured serializer** `printProgram`/`printPolicy` into an
S-expression wire value `Sx`, an inverse **parser** `parseProgram`/`parsePolicy`,
and proves the round-trip

    parseProgram (printProgram p) = some p          (`parse_printProgram`)
    parsePolicy  (printPolicy  q) = some q          (`parse_printPolicy`)

by structural induction, `sorry`-free within the standard axiom trio.

## What this is, and what it is NOT

`docs/mechanization-plan.md` records spec §9 **result 12** as a partially
mechanized presentation-codec round trip with current Haskell conformance
evidence. Its proof strength remains *test-only* — it is not a soundness theorem.
The real conformance evidence for the concrete `.lara` surface syntax is the
Haskell QuickCheck round-trip (`parse ∘ print == id`); a Lean re-implementation
of a *different* codec cannot transfer to the Haskell parser (spec plan A3).
This theorem is therefore a **metatheory anchor for the modeled AST**:
over exactly the surface enumerated under `## Scope` below, it certifies enough
structure to serialize and recover values with no information collapsed.
It is NOT a proof that the concrete-syntax Haskell parser is correct, and it
says nothing about the concrete `.lara` spelling.

Following the sanctioned design guidance (design for provability, not fidelity to
the concrete whitespace/comment syntax), the codec targets a clean structured
S-expression `Sx`, exactly the way the actual wire front end targets a structured
value. This mirrors the existing verified structured codecs in the development:
`Lara.ND.Tag.parse_toString`, `Lara.Strict.decodeFrames_render`,
`Lara.Strict.decodeAtomKey_encodeAtomKey`, `Lara.Strict.decodeTermKeys_encode`.

## Scope

Verified against the complete live presentation `Program`/`Policy` shape of
`src/Lara/AST.hs` at `lara-syntax@0.8`, described here (the model was written
against the `@0.6` AST and still holds verbatim: `@0.7` restricts the concrete
`.lara` surface only — grammar Appendix F — and `@0.8` only widens the name
class a certificate premise reference may carry — grammar Appendix G — so
neither changes a `Lara.AST` type):

* **Both presentation top-levels**: every `Program` field and every `Policy`
  field, `policySigma` included; every arm of `Decl` (including `DeclGroup` and
  `DeclComparison`). `Lara/PresentationParity.lean` pins the `Policy` and
  `Measurand` constructor shapes, so neither can be silently retyped or
  reordered while these round-trip theorems keep passing.
* **Every identifier newtype** of the `Names`, `@0.4`, and `@0.5` sections —
  `PropId`, `QuestionId`, `LeafId`, `RuleId`, `ArgId`, `ArgRef`, `ObligationId`,
  `BackendId`, `PolicyId`, `Param`, `SourceRef`, `TheoryDigest`, `Digest`, `GroupId`,
  `MeasurandId`, `DatasetId`, `PremiseLabel`, `ValueName` — kept as distinct
  one-field structures, so the codec cannot silently swap namespaces (the
  symbolic-core discipline of CLAUDE.md).
* **Every closed enum vocabulary**: `LeafKind`, `Provenance`, `AuditStatus`,
  `Mode`, `Necessity`, `Admission`, `Step`, `GroupConflictMode`, `Polarity`,
  `Relation`, plus `Bool` flags and `Option` fields.
* **The declared signature Σ** — `Sort` (spelled `TermSort`, since `Sort` is a
  Lean keyword), `ConSig`, `PredSig`, `Sigma` — reused verbatim from
  `Lara/Sigma.lean`, the same objects the checker boundary carries. This module
  contributes only their codecs; it defines no parallel presentation-only sort
  or signature vocabulary. `ConSym` and `PredSym` stay distinct newtypes across
  the codec.
* **The recursive spine** — `Pat` / `AtomPat`, and the `SupportTerm` term algebra
  (premises, ground substitution, critical-question discharge map, open holes,
  and assurance) — modeled with bespoke mutual list inductives so `deriving
  DecidableEq` and clean mutual structural recursion both work, exactly as
  `Lara.Prop` does for `Term` / `Terms`.
* **The full record layer**: `Leaf`, `Binding`, `Claim`, `Question`, `CertRef`,
  `Rule` (with `@0.3`'s `rulePremiseLabels`), `Contrary`, `Exception`,
  `DupGroup`, `Measurand`, `ComparisonScheme`, `Policy`, `Cert`, `Assurance`,
  `Attack`, `SurfaceAttack`, `ChallengeTarget`, `ArgConcl`, `Arg`,
  `ComparisonClaim`, `Comparison`, `Decl`, `ValueBinding`, `Program`.
* The opaque strict-certificate payload is carried as an `Sx` verbatim — faithful
  to `Lara.AST`'s "opaque payload, only the named backend decodes it".
* Both the frozen `Attack` / `Position` / `Step` **and** the `@0.3`
  presentation-only `SurfaceAttack` / `SurfaceStep` (grammar §7 AMENDMENT,
  App. B.5). `Decl.attack` carries the *surface* form, matching `DeclAttack`;
  the frozen trio is kept, codec'd, and proved, but is now reachable only from
  the elaborator's output, not from a `Program`.

## What is deliberately NOT here, and the modeling deviations

Not ported, because they are not part of the presentation `Program`/`Policy` and
are mechanized elsewhere in this development:

* `Unit` — the checker-boundary anchor; see `Lara/Unit.lean` and the wire codec
  work, not this module.
* `Status` / `Label` (spec §8) and `RejectClass` / `Rejection` (spec §10.1) —
  checker *outputs*, mirrored by `Lara/Check/Error.lean`.
* The `Assurance'` alias, which is `Assurance` under another name.

Deviations a reader should not mistake for parity:
* `Measurand` round-trips *whatever* `(sort, polarity)` pair it is given.
  `Lara.AST` additionally `Num`-gates the polarity clause (a `where
  higher-is-better` presupposes an ordered domain), so a non-`Num` measurand
  carrying a polarity is a real inhabitant of this Lean type and round-trips
  fine here. That gate is a surface well-formedness check, not a codec property,
  and is not claimed by result 12. The same holds for Σ well-formedness, which
  `Lara.Sigma.sigmaWellFormed` owns.
* Haskell `Prop = Prop Pred [Term]` is this module's `Lara.Atom`, and `Pred` /
  `FunSym` are bare `String`s inside `Atom` / `Pat` / `AtomPat` because that is
  how the frozen Lean semantic core (`Lara.Prop`) already spells them. The
  identifier-newtype discipline above therefore stops at the `Lara.Prop`
  boundary; it is not weakened anywhere this module owns.
* Wire NATs (`certVersion`, `certRefVersion`) and premise indices (`Step`,
  `SurfaceStep`) are `Int`, following the Haskell `Int`.
* `Rule.premiseLabels` round-trips *whatever list it is given*. `Lara.AST`
  additionally declares a canonical form (`[]`, or exactly `premises.length`
  entries with at least one `some`); a non-canonical all-`none` list is a real
  inhabitant of this Lean type and round-trips fine here. Canonicalization is a
  property of the Haskell concrete printer, not of this structured codec, and is
  not claimed by result 12.
* The codec targets the structured `Sx`, not `.lara` concrete syntax; so nothing
  about whitespace, comments, `{cell l}` interpolation, or the `{{`/`}}` brace
  contract is in scope. `ComparisonClaim.nlRaw` is carried as authored bytes
  precisely so that stays true.
-/
import Lara.Prop
import Lara.Sigma

namespace Lara.Presentation

open Lara (Term Terms Atom)

/-! ## The structured wire value `Sx`

A tagged S-expression: a string leaf, an integer leaf, or a tagged node carrying an
ordered child list. `SxList` is the bespoke cons-list mutual with `Sx` (as
`Lara.Prop` does with `Term` / `Terms`) so that `deriving DecidableEq` works and
recursion into children is clean structural recursion. -/
mutual
  inductive Sx where
    | str  : String → Sx
    | int  : Int → Sx
    | node : String → SxList → Sx
  inductive SxList where
    | nil  : SxList
    | cons : Sx → SxList → SxList
end
deriving instance DecidableEq for Sx, SxList

/-! ## Generic list / pair combinators over `Sx`

A homogeneous `List α` serializes to a `"l"`-tagged node whose children are the
element encodings; a pair to a `"p"`-tagged node with two children. Both come with
a round-trip lemma parameterized by the element codec's round-trip, so every
list-valued and pair-valued field reuses one proof. -/

def sxOfList (f : α → Sx) : List α → SxList
  | []      => .nil
  | a :: as => .cons (f a) (sxOfList f as)

def listOfSx (g : Sx → Option α) : SxList → Option (List α)
  | .nil       => some []
  | .cons x xs => do
      let a ← g x
      let as ← listOfSx g xs
      some (a :: as)

theorem listOfSx_sxOfList {f : α → Sx} {g : Sx → Option α}
    (h : ∀ a, g (f a) = some a) (as : List α) :
    listOfSx g (sxOfList f as) = some as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [sxOfList, listOfSx, h a, ih]

def sxList (f : α → Sx) (xs : List α) : Sx := .node "l" (sxOfList f xs)

def unSxList (g : Sx → Option α) : Sx → Option (List α)
  | .node "l" ch => listOfSx g ch
  | _            => none

@[simp] theorem unSxList_sxList {f : α → Sx} {g : Sx → Option α}
    (h : ∀ a, g (f a) = some a) (xs : List α) :
    unSxList g (sxList f xs) = some xs := by
  simp [sxList, unSxList, listOfSx_sxOfList h]

def sxPair {α β : Type} (f : α → Sx) (k : β → Sx) (ab : α × β) : Sx :=
  .node "p" (.cons (f ab.1) (.cons (k ab.2) .nil))

def unSxPair {α β : Type} (g : Sx → Option α) (j : Sx → Option β) : Sx → Option (α × β)
  | .node "p" (.cons x (.cons y .nil)) => do
      let a ← g x
      let b ← j y
      some (a, b)
  | _ => none

@[simp] theorem unSxPair_sxPair {f : α → Sx} {k : β → Sx}
    {g : Sx → Option α} {j : Sx → Option β}
    (hf : ∀ a, g (f a) = some a) (hk : ∀ b, j (k b) = some b) (ab : α × β) :
    unSxPair g j (sxPair f k ab) = some ab := by
  simp [sxPair, unSxPair, hf, hk]

/-- An optional field: `"no"`/`"so"`-tagged nodes. Used by `Rule.premiseLabels`
(`List (Option PremiseLabel)`, grammar App. B.4) and `Comparison.supports`
(`Maybe PropId`, App. B.3). -/
def sxOpt (f : α → Sx) : Option α → Sx
  | none   => .node "no" .nil
  | some a => .node "so" (.cons (f a) .nil)

def unOpt (g : Sx → Option α) : Sx → Option (Option α)
  | .node "no" .nil          => some none
  | .node "so" (.cons x .nil) => do
      let a ← g x
      some (some a)
  | _ => none

@[simp] theorem unOpt_sxOpt {f : α → Sx} {g : Sx → Option α}
    (h : ∀ a, g (f a) = some a) (o : Option α) :
    unOpt g (sxOpt f o) = some o := by
  cases o <;> simp [sxOpt, unOpt, h]

/-! ## Primitive leaves -/

def sxStr (s : String) : Sx := .str s
def unStr : Sx → Option String
  | .str s => some s
  | _      => none
@[simp] theorem unStr_sxStr (s : String) : unStr (sxStr s) = some s := rfl
@[simp] theorem un_sxList_String (xs : List String) :
    unSxList unStr (sxList sxStr xs) = some xs := unSxList_sxList unStr_sxStr xs

def sxInt (n : Int) : Sx := .int n
def unInt : Sx → Option Int
  | .int n => some n
  | _      => none
@[simp] theorem unInt_sxInt (n : Int) : unInt (sxInt n) = some n := rfl

def sxBool : Bool → Sx
  | true  => .node "true" .nil
  | false => .node "false" .nil
def unBool : Sx → Option Bool
  | .node "true"  .nil => some true
  | .node "false" .nil => some false
  | _                  => none
@[simp] theorem unBool_sxBool (b : Bool) : unBool (sxBool b) = some b := by
  cases b <;> rfl

/-! ## Identifier newtypes (spec §2)

Each identifier class is its own one-field structure — distinct types so the codec
cannot silently swap one namespace for another (the symbolic-core discipline of
CLAUDE.md; mirrors the Haskell `newtype`s). Every codec is a trivial wrap of a
string leaf; the round-trip is `rfl`. -/

structure PropId       where mk :: (val : String) deriving DecidableEq
structure QuestionId   where mk :: (val : String) deriving DecidableEq
structure LeafId       where mk :: (val : String) deriving DecidableEq
structure RuleId       where mk :: (val : String) deriving DecidableEq
structure ArgId        where mk :: (val : String) deriving DecidableEq
structure ArgRef       where mk :: (val : String) deriving DecidableEq
structure ObligationId where mk :: (val : String) deriving DecidableEq
structure BackendId    where mk :: (val : String) deriving DecidableEq
structure PolicyId     where mk :: (val : String) deriving DecidableEq
structure Param        where mk :: (val : String) deriving DecidableEq
structure SourceRef    where mk :: (val : String) deriving DecidableEq
structure TheoryDigest where mk :: (val : String) deriving DecidableEq
structure Digest       where mk :: (val : String) deriving DecidableEq
structure GroupId      where mk :: (val : String) deriving DecidableEq
structure MeasurandId  where mk :: (val : String) deriving DecidableEq
structure DatasetId    where mk :: (val : String) deriving DecidableEq
structure PremiseLabel where mk :: (val : String) deriving DecidableEq
structure ValueName    where mk :: (val : String) deriving DecidableEq

def PropId.sx       (i : PropId)       : Sx := .str i.val
def QuestionId.sx   (i : QuestionId)   : Sx := .str i.val
def LeafId.sx       (i : LeafId)       : Sx := .str i.val
def RuleId.sx       (i : RuleId)       : Sx := .str i.val
def ArgId.sx        (i : ArgId)        : Sx := .str i.val
def ArgRef.sx       (i : ArgRef)       : Sx := .str i.val
def ObligationId.sx (i : ObligationId) : Sx := .str i.val
def BackendId.sx    (i : BackendId)    : Sx := .str i.val
def PolicyId.sx     (i : PolicyId)     : Sx := .str i.val
def Param.sx        (i : Param)        : Sx := .str i.val
def SourceRef.sx    (i : SourceRef)    : Sx := .str i.val
def TheoryDigest.sx (i : TheoryDigest) : Sx := .str i.val
def Digest.sx       (i : Digest)       : Sx := .str i.val
def GroupId.sx      (i : GroupId)      : Sx := .str i.val
def MeasurandId.sx  (i : MeasurandId)  : Sx := .str i.val
def DatasetId.sx    (i : DatasetId)    : Sx := .str i.val
def PremiseLabel.sx (i : PremiseLabel) : Sx := .str i.val
def ValueName.sx    (i : ValueName)    : Sx := .str i.val

def unPropId       : Sx → Option PropId       | .str s => some ⟨s⟩ | _ => none
def unQuestionId   : Sx → Option QuestionId   | .str s => some ⟨s⟩ | _ => none
def unLeafId       : Sx → Option LeafId       | .str s => some ⟨s⟩ | _ => none
def unRuleId       : Sx → Option RuleId       | .str s => some ⟨s⟩ | _ => none
def unArgId        : Sx → Option ArgId        | .str s => some ⟨s⟩ | _ => none
def unArgRef       : Sx → Option ArgRef       | .str s => some ⟨s⟩ | _ => none
def unObligationId : Sx → Option ObligationId | .str s => some ⟨s⟩ | _ => none
def unBackendId    : Sx → Option BackendId    | .str s => some ⟨s⟩ | _ => none
def unPolicyId     : Sx → Option PolicyId     | .str s => some ⟨s⟩ | _ => none
def unParam        : Sx → Option Param        | .str s => some ⟨s⟩ | _ => none
def unSourceRef    : Sx → Option SourceRef    | .str s => some ⟨s⟩ | _ => none
def unTheoryDigest : Sx → Option TheoryDigest | .str s => some ⟨s⟩ | _ => none
def unDigest       : Sx → Option Digest       | .str s => some ⟨s⟩ | _ => none
def unGroupId      : Sx → Option GroupId      | .str s => some ⟨s⟩ | _ => none
def unMeasurandId  : Sx → Option MeasurandId  | .str s => some ⟨s⟩ | _ => none
def unDatasetId    : Sx → Option DatasetId    | .str s => some ⟨s⟩ | _ => none
def unPremiseLabel : Sx → Option PremiseLabel | .str s => some ⟨s⟩ | _ => none
def unValueName    : Sx → Option ValueName    | .str s => some ⟨s⟩ | _ => none

@[simp] theorem un_PropId       (i : PropId)       : unPropId       i.sx = some i := rfl
@[simp] theorem un_QuestionId   (i : QuestionId)   : unQuestionId   i.sx = some i := rfl
@[simp] theorem un_LeafId       (i : LeafId)       : unLeafId       i.sx = some i := rfl
@[simp] theorem un_RuleId       (i : RuleId)       : unRuleId       i.sx = some i := rfl
@[simp] theorem un_ArgId        (i : ArgId)        : unArgId        i.sx = some i := rfl
@[simp] theorem un_ArgRef       (i : ArgRef)       : unArgRef       i.sx = some i := rfl
@[simp] theorem un_ObligationId (i : ObligationId) : unObligationId i.sx = some i := rfl
@[simp] theorem un_BackendId    (i : BackendId)    : unBackendId    i.sx = some i := rfl
@[simp] theorem un_PolicyId     (i : PolicyId)     : unPolicyId     i.sx = some i := rfl
@[simp] theorem un_Param        (i : Param)        : unParam        i.sx = some i := rfl
@[simp] theorem un_SourceRef    (i : SourceRef)    : unSourceRef    i.sx = some i := rfl
@[simp] theorem un_TheoryDigest (i : TheoryDigest) : unTheoryDigest i.sx = some i := rfl
@[simp] theorem un_Digest       (i : Digest)       : unDigest       i.sx = some i := rfl
@[simp] theorem un_GroupId      (i : GroupId)      : unGroupId      i.sx = some i := rfl
@[simp] theorem un_MeasurandId  (i : MeasurandId)  : unMeasurandId  i.sx = some i := rfl
@[simp] theorem un_DatasetId    (i : DatasetId)    : unDatasetId    i.sx = some i := rfl
@[simp] theorem un_PremiseLabel (i : PremiseLabel) : unPremiseLabel i.sx = some i := rfl
@[simp] theorem un_ValueName    (i : ValueName)    : unValueName    i.sx = some i := rfl

@[simp] theorem un_sxList_LeafId (xs : List LeafId) :
    unSxList unLeafId (sxList LeafId.sx xs) = some xs := unSxList_sxList un_LeafId xs
@[simp] theorem un_sxList_ArgRef (xs : List ArgRef) :
    unSxList unArgRef (sxList ArgRef.sx xs) = some xs := unSxList_sxList un_ArgRef xs
@[simp] theorem un_sxOpt_PremiseLabel (o : Option PremiseLabel) :
    unOpt unPremiseLabel (sxOpt PremiseLabel.sx o) = some o := unOpt_sxOpt un_PremiseLabel o
@[simp] theorem un_sxList_optPremiseLabel (xs : List (Option PremiseLabel)) :
    unSxList (unOpt unPremiseLabel) (sxList (sxOpt PremiseLabel.sx) xs) = some xs :=
  unSxList_sxList un_sxOpt_PremiseLabel xs
abbrev ArgDischarge := List (QuestionId × ArgRef)
def sxArgDischarge (ds : ArgDischarge) : Sx :=
  sxList (sxPair QuestionId.sx ArgRef.sx) ds
def unArgDischarge : Sx → Option ArgDischarge :=
  unSxList (unSxPair unQuestionId unArgRef)
@[simp] theorem un_sxArgDischarge (ds : ArgDischarge) :
    unArgDischarge (sxArgDischarge ds) = some ds :=
  unSxList_sxList (unSxPair_sxPair un_QuestionId un_ArgRef) ds

@[simp] theorem un_sxOpt_PropId (o : Option PropId) :
    unOpt unPropId (sxOpt PropId.sx o) = some o := unOpt_sxOpt un_PropId o

/-! ## Closed enum vocabularies (spec §3, §4, §7, §8)

Each finite vocabulary is a closed sum encoded as a tagged node — never a bare
string literal at the codec boundary. `Provenance.checker` and `Step.premise`
carry payloads. -/

inductive LeafKind   where | observed | attested | assumed | certified deriving DecidableEq
inductive Provenance where | user | aiExecuted | checker : String → String → Provenance deriving DecidableEq
inductive AuditStatus where | unreviewed | reviewed | disputed deriving DecidableEq
inductive Mode       where | strict | defeasible deriving DecidableEq
inductive Necessity  where | mandatory | optional deriving DecidableEq
inductive Admission  where | admit | quarantine | reject deriving DecidableEq
/-- Policy outcome for a duplicate-report group whose members are not pairwise `≡`
(spec §4.3). -/
inductive GroupConflictMode where | quarantineOnConflict | rejectOnConflict deriving DecidableEq
/-- Which direction of a measurand is the better result (grammar App. B.1). -/
inductive Polarity   where | higherIsBetter | lowerIsBetter deriving DecidableEq
/-- The comparative relation a `comparison` block asserts (grammar App. B.2, B.3). -/
inductive Relation   where | strictlyBetter | atLeastAsGood deriving DecidableEq

def LeafKind.sx : LeafKind → Sx
  | .observed  => .node "observed"  .nil
  | .attested  => .node "attested"  .nil
  | .assumed   => .node "assumed"   .nil
  | .certified => .node "certified" .nil
def unLeafKind : Sx → Option LeafKind
  | .node "observed"  .nil => some .observed
  | .node "attested"  .nil => some .attested
  | .node "assumed"   .nil => some .assumed
  | .node "certified" .nil => some .certified
  | _ => none
@[simp] theorem un_LeafKind (k : LeafKind) : unLeafKind k.sx = some k := by cases k <;> rfl

def Provenance.sx : Provenance → Sx
  | .user       => .node "user" .nil
  | .aiExecuted => .node "ai" .nil
  | .checker n v => .node "checker" (.cons (.str n) (.cons (.str v) .nil))
def unProvenance : Sx → Option Provenance
  | .node "user" .nil => some .user
  | .node "ai"   .nil => some .aiExecuted
  | .node "checker" (.cons (.str n) (.cons (.str v) .nil)) => some (.checker n v)
  | _ => none
@[simp] theorem un_Provenance (p : Provenance) : unProvenance p.sx = some p := by cases p <;> rfl

def AuditStatus.sx : AuditStatus → Sx
  | .unreviewed => .node "unreviewed" .nil
  | .reviewed   => .node "reviewed" .nil
  | .disputed   => .node "disputed" .nil
def unAuditStatus : Sx → Option AuditStatus
  | .node "unreviewed" .nil => some .unreviewed
  | .node "reviewed"   .nil => some .reviewed
  | .node "disputed"   .nil => some .disputed
  | _ => none
@[simp] theorem un_AuditStatus (a : AuditStatus) : unAuditStatus a.sx = some a := by cases a <;> rfl

def Mode.sx : Mode → Sx
  | .strict     => .node "strict" .nil
  | .defeasible => .node "defeasible" .nil
def unMode : Sx → Option Mode
  | .node "strict"     .nil => some .strict
  | .node "defeasible" .nil => some .defeasible
  | _ => none
@[simp] theorem un_Mode (m : Mode) : unMode m.sx = some m := by cases m <;> rfl

def Necessity.sx : Necessity → Sx
  | .mandatory => .node "mandatory" .nil
  | .optional  => .node "optional" .nil
def unNecessity : Sx → Option Necessity
  | .node "mandatory" .nil => some .mandatory
  | .node "optional"  .nil => some .optional
  | _ => none
@[simp] theorem un_Necessity (n : Necessity) : unNecessity n.sx = some n := by cases n <;> rfl

def Admission.sx : Admission → Sx
  | .admit      => .node "admit" .nil
  | .quarantine => .node "quarantine" .nil
  | .reject     => .node "reject" .nil
def unAdmission : Sx → Option Admission
  | .node "admit"      .nil => some .admit
  | .node "quarantine" .nil => some .quarantine
  | .node "reject"     .nil => some .reject
  | _ => none
@[simp] theorem un_Admission (a : Admission) : unAdmission a.sx = some a := by cases a <;> rfl

def GroupConflictMode.sx : GroupConflictMode → Sx
  | .quarantineOnConflict => .node "gq" .nil
  | .rejectOnConflict     => .node "gr" .nil
def unGroupConflictMode : Sx → Option GroupConflictMode
  | .node "gq" .nil => some .quarantineOnConflict
  | .node "gr" .nil => some .rejectOnConflict
  | _ => none
@[simp] theorem un_GroupConflictMode (m : GroupConflictMode) :
    unGroupConflictMode m.sx = some m := by cases m <;> rfl

def Polarity.sx : Polarity → Sx
  | .higherIsBetter => .node "hib" .nil
  | .lowerIsBetter  => .node "lib" .nil
def unPolarity : Sx → Option Polarity
  | .node "hib" .nil => some .higherIsBetter
  | .node "lib" .nil => some .lowerIsBetter
  | _ => none
@[simp] theorem un_Polarity (p : Polarity) : unPolarity p.sx = some p := by cases p <;> rfl

@[simp] theorem un_sxOpt_Polarity (o : Option Polarity) :
    unOpt unPolarity (sxOpt Polarity.sx o) = some o := unOpt_sxOpt un_Polarity o

def Relation.sx : Relation → Sx
  | .strictlyBetter => .node "sb" .nil
  | .atLeastAsGood  => .node "alag" .nil
def unRelation : Sx → Option Relation
  | .node "sb"   .nil => some .strictlyBetter
  | .node "alag" .nil => some .atLeastAsGood
  | _ => none
@[simp] theorem un_Relation (r : Relation) : unRelation r.sx = some r := by cases r <;> rfl

/-! ## The declared signature Σ (spec §2, §3.4, reused semantic core `Lara.Sigma`)

`Policy.sigma` and `Measurand.sort` are the *same* Σ object the checker boundary
carries, not a presentation-only echo of it: the types below are literally
`Lara.Sigma`'s, aliased here only so this module reads in one vocabulary. A
parallel presentation sort/signature vocabulary would be exactly the silent
namespace split the symbolic-core discipline forbids.

`Sort` is a Lean keyword, so the sort of a term is spelled `TermSort` — the same
collision `Lara.Sigma` already handles. `ConSym` / `PredSym` stay distinct
newtypes across the codec: each is encoded through its `name` and rebuilt at its
own type, never collapsed into one string namespace. -/

abbrev TermSort := Lara.Sigma.TermSort
abbrev ConSig   := Lara.Sigma.ConSig
abbrev PredSig  := Lara.Sigma.PredSig
abbrev Sigma    := Lara.Sigma.Sigma

def sxTermSort : TermSort → Sx
  | .num    => .node "sort-num" .nil
  | .str    => .node "sort-str" .nil
  | .decl n => .node "sort-decl" (.cons (.str n) .nil)
def unTermSort : Sx → Option TermSort
  | .node "sort-num"  .nil                  => some .num
  | .node "sort-str"  .nil                  => some .str
  | .node "sort-decl" (.cons (.str n) .nil) => some (.decl n)
  | _ => none
@[simp] theorem un_TermSort (s : TermSort) : unTermSort (sxTermSort s) = some s := by
  cases s <;> rfl
@[simp] theorem un_sxList_TermSort (xs : List TermSort) :
    unSxList unTermSort (sxList sxTermSort xs) = some xs := unSxList_sxList un_TermSort xs

/-- `con k(s₁,…,sₙ) : s`. -/
def sxConSig (c : ConSig) : Sx :=
  .node "con-sig" (.cons (.str c.sym.name)
    (.cons (sxList sxTermSort c.args) (.cons (sxTermSort c.result) .nil)))
def unConSig : Sx → Option ConSig
  | .node "con-sig" (.cons (.str k) (.cons ar (.cons rs .nil))) => do
      let aa ← unSxList unTermSort ar
      let rr ← unTermSort rs
      some ⟨⟨k⟩, aa, rr⟩
  | _ => none
@[simp] theorem un_sxConSig (c : ConSig) : unConSig (sxConSig c) = some c := by
  cases c with | mk sym args result => simp [sxConSig, unConSig]
@[simp] theorem un_sxList_ConSig (xs : List ConSig) :
    unSxList unConSig (sxList sxConSig xs) = some xs := unSxList_sxList un_sxConSig xs

/-- `pred p(s₁,…,sₙ)`. Predicates have no result sort, which is why they are a
separate table from the constructors. -/
def sxPredSig (p : PredSig) : Sx :=
  .node "pred-sig" (.cons (.str p.sym.name) (.cons (sxList sxTermSort p.args) .nil))
def unPredSig : Sx → Option PredSig
  | .node "pred-sig" (.cons (.str q) (.cons ar .nil)) => do
      let aa ← unSxList unTermSort ar
      some ⟨⟨q⟩, aa⟩
  | _ => none
@[simp] theorem un_sxPredSig (p : PredSig) : unPredSig (sxPredSig p) = some p := by
  cases p with | mk sym args => simp [sxPredSig, unPredSig]
@[simp] theorem un_sxList_PredSig (xs : List PredSig) :
    unSxList unPredSig (sxList sxPredSig xs) = some xs := unSxList_sxList un_sxPredSig xs

/-- The whole signature: declared sorts, then the constructor and predicate
tables. Declaration order is retained, so the encoding is canonical. -/
def sxSigma (sg : Sigma) : Sx :=
  .node "sigma" (.cons (sxList sxStr sg.sorts)
    (.cons (sxList sxConSig sg.cons) (.cons (sxList sxPredSig sg.preds) .nil)))
def unSigma : Sx → Option Sigma
  | .node "sigma" (.cons ss (.cons cs (.cons ps .nil))) => do
      let sorts ← unSxList unStr ss
      let cons  ← unSxList unConSig cs
      let preds ← unSxList unPredSig ps
      some ⟨sorts, cons, preds⟩
  | _ => none
@[simp] theorem un_sxSigma (sg : Sigma) : unSigma (sxSigma sg) = some sg := by
  cases sg with | mk sorts cons preds => simp [sxSigma, unSigma]

/-! ## Propositions (spec §2, reused semantic core `Lara.Prop`)

Ground terms, their argument lists, and atoms are the frozen `Lara.Term` /
`Lara.Terms` / `Lara.Atom`. A `Terms` argument list serializes directly as the
tail children of its constructor node, so parsing is clean mutual structural
recursion — no length prefix. -/

mutual
  def sxTerm : Term → Sx
    | .num s    => .node "tn" (.cons (.str s) .nil)
    | .str s    => .node "ts" (.cons (.str s) .nil)
    | .con k ts => .node "tc" (.cons (.str k) (sxTerms ts))
  def sxTerms : Terms → SxList
    | .nil       => .nil
    | .cons t ts => .cons (sxTerm t) (sxTerms ts)
end

mutual
  def unTerm : Sx → Option Term
    | .node "tn" (.cons (.str s) .nil) => some (.num s)
    | .node "ts" (.cons (.str s) .nil) => some (.str s)
    | .node "tc" (.cons (.str k) rest) => do
        let ts ← unTerms rest
        some (.con k ts)
    | _ => none
  def unTerms : SxList → Option Terms
    | .nil       => some .nil
    | .cons x xs => do
        let t  ← unTerm x
        let ts ← unTerms xs
        some (.cons t ts)
end

mutual
  @[simp] theorem un_sxTerm (t : Term) : unTerm (sxTerm t) = some t := by
    match t with
    | .num s    => rfl
    | .str s    => rfl
    | .con k ts => simp [sxTerm, unTerm, un_sxTerms ts]
  @[simp] theorem un_sxTerms (ts : Terms) : unTerms (sxTerms ts) = some ts := by
    match ts with
    | .nil       => rfl
    | .cons t ts => simp [sxTerms, unTerms, un_sxTerm t, un_sxTerms ts]
end

def sxAtom : Atom → Sx
  | .atom p ts => .node "atom" (.cons (.str p) (sxTerms ts))
def unAtom : Sx → Option Atom
  | .node "atom" (.cons (.str p) rest) => do
      let ts ← unTerms rest
      some (.atom p ts)
  | _ => none
@[simp] theorem un_sxAtom (a : Atom) : unAtom (sxAtom a) = some a := by
  cases a with
  | atom p ts => simp [sxAtom, unAtom, un_sxTerms ts]

@[simp] theorem un_sxList_Atom (xs : List Atom) :
    unSxList unAtom (sxList sxAtom xs) = some xs := unSxList_sxList un_sxAtom xs

/-- A trusted-theory table entry `(digest, [prop])` (grammar App. A.2). -/
abbrev TheoryEntry := TheoryDigest × List Atom
def sxTheoryEntry (e : TheoryEntry) : Sx := sxPair TheoryDigest.sx (sxList sxAtom) e
def unTheoryEntry : Sx → Option TheoryEntry := unSxPair unTheoryDigest (unSxList unAtom)
@[simp] theorem un_sxTheoryEntry (e : TheoryEntry) : unTheoryEntry (sxTheoryEntry e) = some e :=
  unSxPair_sxPair un_TheoryDigest un_sxList_Atom e
@[simp] theorem un_sxList_TheoryEntry (xs : List TheoryEntry) :
    unSxList unTheoryEntry (sxList sxTheoryEntry xs) = some xs :=
  unSxList_sxList un_sxTheoryEntry xs

/-! ## Patterns (spec §4.1)

`Pat ::= X | k | k(P…)`; `AtomPat ::= pred(P₁,…,Pₙ)`. The constructor-argument
recursion uses a bespoke mutual `Pats` list (as `Terms` does), so `deriving
DecidableEq` and structural recursion both work. `FunSym` / `Pred` are the frozen
`String` names of the semantic core. -/

mutual
  inductive Pat where
    | var : Param → Pat
    | lit : Term → Pat
    | con : String → Pats → Pat
  inductive Pats where
    | nil  : Pats
    | cons : Pat → Pats → Pats
end
deriving instance DecidableEq for Pat, Pats

structure AtomPat where mk :: (pred : String) (args : Pats) deriving DecidableEq

mutual
  def sxPat : Pat → Sx
    | .var x    => .node "pv" (.cons (.str x.val) .nil)
    | .lit t    => .node "pl" (.cons (sxTerm t) .nil)
    | .con k ps => .node "pc" (.cons (.str k) (sxPats ps))
  def sxPats : Pats → SxList
    | .nil       => .nil
    | .cons p ps => .cons (sxPat p) (sxPats ps)
end

mutual
  def unPat : Sx → Option Pat
    | .node "pv" (.cons (.str x) .nil) => some (.var ⟨x⟩)
    | .node "pl" (.cons t .nil)        => do
        let t' ← unTerm t
        some (.lit t')
    | .node "pc" (.cons (.str k) rest) => do
        let ps ← unPats rest
        some (.con k ps)
    | _ => none
  def unPats : SxList → Option Pats
    | .nil       => some .nil
    | .cons x xs => do
        let p  ← unPat x
        let ps ← unPats xs
        some (.cons p ps)
end

mutual
  @[simp] theorem un_sxPat (p : Pat) : unPat (sxPat p) = some p := by
    match p with
    | .var x    => rfl
    | .lit t    => simp [sxPat, unPat]
    | .con k ps => simp [sxPat, unPat, un_sxPats ps]
  @[simp] theorem un_sxPats (ps : Pats) : unPats (sxPats ps) = some ps := by
    match ps with
    | .nil       => rfl
    | .cons p ps => simp [sxPats, unPats, un_sxPat p, un_sxPats ps]
end

def sxAtomPat (a : AtomPat) : Sx := .node "apat" (.cons (.str a.pred) (sxPats a.args))
def unAtomPat : Sx → Option AtomPat
  | .node "apat" (.cons (.str p) rest) => do
      let ps ← unPats rest
      some ⟨p, ps⟩
  | _ => none
@[simp] theorem un_sxAtomPat (a : AtomPat) : unAtomPat (sxAtomPat a) = some a := by
  cases a with
  | mk p ps => simp [sxAtomPat, unAtomPat, un_sxPats ps]

/-! ## Certificates and assurance (spec §5, §6)

The strict-certificate payload is carried as an `Sx` verbatim — faithful to
`Lara.AST`'s opaque `SExpr` payload that only the named backend decodes; the codec
never inspects it. `Assurance` is the closed three-way tag. -/

structure Cert where
  mk ::
  (backend : BackendId)
  (version : Int)
  (theory : TheoryDigest)
  (payload : Sx)
  deriving DecidableEq

def sxCert (c : Cert) : Sx :=
  .node "cert" (.cons c.backend.sx (.cons (.int c.version)
    (.cons c.theory.sx (.cons c.payload .nil))))
def unCert : Sx → Option Cert
  | .node "cert" (.cons b (.cons (.int v) (.cons th (.cons pl .nil)))) => do
      let bb ← unBackendId b
      let tt ← unTheoryDigest th
      some ⟨bb, v, tt, pl⟩
  | _ => none
@[simp] theorem un_sxCert (c : Cert) : unCert (sxCert c) = some c := by
  cases c with
  | mk b v t p => simp [sxCert, unCert]

inductive Assurance where
  | none    : Assurance
  | trusted : Assurance
  | cert    : Cert → Assurance
  deriving DecidableEq

def sxAssurance : Assurance → Sx
  | .none    => .node "an" .nil
  | .trusted => .node "at" .nil
  | .cert c  => .node "ac" (.cons (sxCert c) .nil)
def unAssurance : Sx → Option Assurance
  | .node "an" .nil        => some .none
  | .node "at" .nil        => some .trusted
  | .node "ac" (.cons c .nil) => do
      let cc ← unCert c
      some (.cert cc)
  | _ => none
@[simp] theorem un_sxAssurance (a : Assurance) : unAssurance (sxAssurance a) = some a := by
  cases a with
  | none => rfl
  | trusted => rfl
  | cert c => simp [sxAssurance, unAssurance]

/-! ## Support terms (spec §6)

`w ::= leaf l | r⟨θ ; w₁,…,wₙ ; {q ↦ w_q} ; {o*} ; assurance⟩`. The premise list
and the critical-question discharge map recurse into `SupportTerm`, so they are
bespoke mutual list inductives (`SupportTerms`, `Discharges`) — the ground
substitution and open-hole set are ordinary lists of already-codec'd elements. -/

abbrev Subst := List (Param × Term)

mutual
  inductive SupportTerm where
    | leaf : LeafId → SupportTerm
    | rule : RuleId → Subst → SupportTerms → Discharges → List ObligationId → Assurance → SupportTerm
  inductive SupportTerms where
    | nil  : SupportTerms
    | cons : SupportTerm → SupportTerms → SupportTerms
  inductive Discharges where
    | nil  : Discharges
    | cons : QuestionId → SupportTerm → Discharges → Discharges
end
deriving instance DecidableEq for SupportTerm, SupportTerms, Discharges

def sxSubst (s : Subst) : Sx := sxList (sxPair (fun p => Param.sx p) sxTerm) s
def unSubst : Sx → Option Subst := unSxList (unSxPair unParam unTerm)
@[simp] theorem un_sxSubst (s : Subst) : unSubst (sxSubst s) = some s := by
  apply unSxList_sxList
  intro ab
  exact unSxPair_sxPair un_Param un_sxTerm ab

def sxHoles (h : List ObligationId) : Sx := sxList ObligationId.sx h
def unHoles : Sx → Option (List ObligationId) := unSxList unObligationId
@[simp] theorem un_sxHoles (h : List ObligationId) : unHoles (sxHoles h) = some h := by
  apply unSxList_sxList
  intro a
  exact un_ObligationId a

mutual
  def sxST : SupportTerm → Sx
    | .leaf l => .node "sl" (.cons l.sx .nil)
    | .rule r sub prems dis holes asr =>
        .node "sr" (.cons r.sx (.cons (sxSubst sub)
          (.cons (.node "prems" (sxSTs prems))
          (.cons (.node "dis" (sxDis dis))
          (.cons (sxHoles holes) (.cons (sxAssurance asr) .nil))))))
  def sxSTs : SupportTerms → SxList
    | .nil       => .nil
    | .cons w ws => .cons (sxST w) (sxSTs ws)
  def sxDis : Discharges → SxList
    | .nil        => .nil
    | .cons q w ds => .cons (.node "d" (.cons q.sx (.cons (sxST w) .nil))) (sxDis ds)
end

mutual
  def unST : Sx → Option SupportTerm
    | .node "sl" (.cons l .nil) => do
        let ll ← unLeafId l
        some (.leaf ll)
    | .node "sr" (.cons r (.cons subS
        (.cons (.node "prems" premsS)
        (.cons (.node "dis" disS)
        (.cons holesS (.cons asrS .nil)))))) => do
        let rr    ← unRuleId r
        let sub   ← unSubst subS
        let prems ← unSTs premsS
        let dis   ← unDis disS
        let holes ← unHoles holesS
        let asr   ← unAssurance asrS
        some (.rule rr sub prems dis holes asr)
    | _ => none
  def unSTs : SxList → Option SupportTerms
    | .nil       => some .nil
    | .cons x xs => do
        let w  ← unST x
        let ws ← unSTs xs
        some (.cons w ws)
  def unDis : SxList → Option Discharges
    | .nil => some .nil
    | .cons (.node "d" (.cons q (.cons w .nil))) xs => do
        let qq ← unQuestionId q
        let ww ← unST w
        let ds ← unDis xs
        some (.cons qq ww ds)
    | .cons _ _ => none
end

mutual
  @[simp] theorem un_sxST (w : SupportTerm) : unST (sxST w) = some w := by
    match w with
    | .leaf l => simp [sxST, unST]
    | .rule r sub prems dis holes asr =>
        simp [sxST, unST, un_sxSubst sub, un_sxHoles holes,
          un_sxSTs prems, un_sxDis dis]
  @[simp] theorem un_sxSTs (ws : SupportTerms) : unSTs (sxSTs ws) = some ws := by
    match ws with
    | .nil       => rfl
    | .cons w ws => simp [sxSTs, unSTs, un_sxST w, un_sxSTs ws]
  @[simp] theorem un_sxDis (ds : Discharges) : unDis (sxDis ds) = some ds := by
    match ds with
    | .nil        => rfl
    | .cons q w ds => simp [sxDis, unDis, un_sxST w, un_sxDis ds]
end

/-! ## Homogeneous list-field round-trips

Each list-valued record field reuses the generic `unSxList_sxList` at its element
codec, packaged as one `@[simp]` lemma so the record proofs close by `simp`. -/

@[simp] theorem un_sxList_SourceRef (xs : List SourceRef) :
    unSxList unSourceRef (sxList SourceRef.sx xs) = some xs := unSxList_sxList un_SourceRef xs
@[simp] theorem un_sxList_Param (xs : List Param) :
    unSxList unParam (sxList Param.sx xs) = some xs := unSxList_sxList un_Param xs
@[simp] theorem un_sxList_AtomPat (xs : List AtomPat) :
    unSxList unAtomPat (sxList sxAtomPat xs) = some xs := unSxList_sxList un_sxAtomPat xs

/-! ## Record layer (spec §3, §4) -/

structure Leaf where
  mk :: (id : LeafId) (prop : Atom) (kind : LeafKind) (provenance : Provenance) (refs : List SourceRef)
  deriving DecidableEq
def sxLeaf (l : Leaf) : Sx :=
  .node "leaf" (.cons l.id.sx (.cons (sxAtom l.prop) (.cons l.kind.sx
    (.cons l.provenance.sx (.cons (sxList SourceRef.sx l.refs) .nil)))))
def unLeaf : Sx → Option Leaf
  | .node "leaf" (.cons i (.cons pr (.cons k (.cons pv (.cons rf .nil))))) => do
      let ii ← unLeafId i
      let pp ← unAtom pr
      let kk ← unLeafKind k
      let vv ← unProvenance pv
      let rr ← unSxList unSourceRef rf
      some ⟨ii, pp, kk, vv, rr⟩
  | _ => none
@[simp] theorem un_sxLeaf (l : Leaf) : unLeaf (sxLeaf l) = some l := by
  cases l with | mk i p k v r => simp [sxLeaf, unLeaf]

structure Binding where
  mk :: (author : String) (rationale : String) (auditStatus : AuditStatus)
  deriving DecidableEq
def sxBinding (b : Binding) : Sx :=
  .node "bind" (.cons (.str b.author) (.cons (.str b.rationale) (.cons b.auditStatus.sx .nil)))
def unBinding : Sx → Option Binding
  | .node "bind" (.cons (.str a) (.cons (.str r) (.cons au .nil))) => do
      let auu ← unAuditStatus au
      some ⟨a, r, auu⟩
  | _ => none
@[simp] theorem un_sxBinding (b : Binding) : unBinding (sxBinding b) = some b := by
  cases b with | mk a r au => simp [sxBinding, unBinding]

structure Claim where
  mk :: (id : PropId) (nl : String) (formal : Atom) (binding : Binding)
  deriving DecidableEq
def sxClaim (c : Claim) : Sx :=
  .node "claim" (.cons c.id.sx (.cons (.str c.nl) (.cons (sxAtom c.formal) (.cons (sxBinding c.binding) .nil))))
def unClaim : Sx → Option Claim
  | .node "claim" (.cons i (.cons (.str nl) (.cons f (.cons bd .nil)))) => do
      let ii ← unPropId i
      let ff ← unAtom f
      let bb ← unBinding bd
      some ⟨ii, nl, ff, bb⟩
  | _ => none
@[simp] theorem un_sxClaim (c : Claim) : unClaim (sxClaim c) = some c := by
  cases c with | mk i nl f b => simp [sxClaim, unClaim]

structure Question where
  mk :: (id : QuestionId) (answer : AtomPat) (necessity : Necessity)
  deriving DecidableEq
def sxQuestion (q : Question) : Sx :=
  .node "q" (.cons q.id.sx (.cons (sxAtomPat q.answer) (.cons q.necessity.sx .nil)))
def unQuestion : Sx → Option Question
  | .node "q" (.cons i (.cons an (.cons nc .nil))) => do
      let ii ← unQuestionId i
      let aa ← unAtomPat an
      let nn ← unNecessity nc
      some ⟨ii, aa, nn⟩
  | _ => none
@[simp] theorem un_sxQuestion (q : Question) : unQuestion (sxQuestion q) = some q := by
  cases q with | mk i a n => simp [sxQuestion, unQuestion]
@[simp] theorem un_sxList_Question (xs : List Question) :
    unSxList unQuestion (sxList sxQuestion xs) = some xs := unSxList_sxList un_sxQuestion xs

structure CertRef where
  mk :: (backend : BackendId) (version : Int) (theory : TheoryDigest)
  deriving DecidableEq
def sxCertRef (c : CertRef) : Sx :=
  .node "cref" (.cons c.backend.sx (.cons (.int c.version) (.cons c.theory.sx .nil)))
def unCertRef : Sx → Option CertRef
  | .node "cref" (.cons b (.cons (.int v) (.cons th .nil))) => do
      let bb ← unBackendId b
      let tt ← unTheoryDigest th
      some ⟨bb, v, tt⟩
  | _ => none
@[simp] theorem un_sxCertRef (c : CertRef) : unCertRef (sxCertRef c) = some c := by
  cases c with | mk b v t => simp [sxCertRef, unCertRef]
@[simp] theorem un_sxList_CertRef (xs : List CertRef) :
    unSxList unCertRef (sxList sxCertRef xs) = some xs := unSxList_sxList un_sxCertRef xs

/-- A named inference scheme (spec §4).

`premiseLabels` is the `lara-syntax@0.3` presentation-only field of grammar
App. B.4, positionally aligned with `premises`: either `[]` (no premise is
labelled — the `@0.2` spelling) or exactly `premises.length` entries. It is a
*parallel* field, never a change to `premises`, because `premises` is
Unit-reachable and frozen. The codec below round-trips whatever list it is
given; canonicalization (a non-empty all-`none` list prints as the unlabelled
spelling) is a Haskell-printer concern outside this structured codec. -/
structure Rule where
  mk ::
  (id : RuleId) (params : List Param) (mode : Mode) (premises : List AtomPat)
  (premiseLabels : List (Option PremiseLabel))
  (conclusion : AtomPat) (allowTrusted : Bool) (certifiers : List CertRef) (questions : List Question)
  deriving DecidableEq
def sxRule (r : Rule) : Sx :=
  .node "rule" (.cons r.id.sx (.cons (sxList Param.sx r.params) (.cons r.mode.sx
    (.cons (sxList sxAtomPat r.premises) (.cons (sxList (sxOpt PremiseLabel.sx) r.premiseLabels)
    (.cons (sxAtomPat r.conclusion)
    (.cons (sxBool r.allowTrusted) (.cons (sxList sxCertRef r.certifiers)
    (.cons (sxList sxQuestion r.questions) .nil)))))))))
def unRule : Sx → Option Rule
  | .node "rule" (.cons i (.cons ps (.cons md (.cons pr (.cons pls (.cons cn (.cons at' (.cons cf (.cons qs .nil))))))))) => do
      let ii ← unRuleId i
      let pp ← unSxList unParam ps
      let mm ← unMode md
      let rr ← unSxList unAtomPat pr
      let ll ← unSxList (unOpt unPremiseLabel) pls
      let cc ← unAtomPat cn
      let aa ← unBool at'
      let ff ← unSxList unCertRef cf
      let qq ← unSxList unQuestion qs
      some ⟨ii, pp, mm, rr, ll, cc, aa, ff, qq⟩
  | _ => none
@[simp] theorem un_sxRule (r : Rule) : unRule (sxRule r) = some r := by
  cases r with | mk i ps md pr pls cn a cf qs => simp [sxRule, unRule]
@[simp] theorem un_sxList_Rule (xs : List Rule) :
    unSxList unRule (sxList sxRule xs) = some xs := unSxList_sxList un_sxRule xs

structure Contrary where mk :: (left : AtomPat) (right : AtomPat) deriving DecidableEq
def sxContrary (c : Contrary) : Sx :=
  .node "contra" (.cons (sxAtomPat c.left) (.cons (sxAtomPat c.right) .nil))
def unContrary : Sx → Option Contrary
  | .node "contra" (.cons l (.cons r .nil)) => do
      let ll ← unAtomPat l
      let rr ← unAtomPat r
      some ⟨ll, rr⟩
  | _ => none
@[simp] theorem un_sxContrary (c : Contrary) : unContrary (sxContrary c) = some c := by
  cases c with | mk l r => simp [sxContrary, unContrary]
@[simp] theorem un_sxList_Contrary (xs : List Contrary) :
    unSxList unContrary (sxList sxContrary xs) = some xs := unSxList_sxList un_sxContrary xs

structure Exception where mk :: (rule : RuleId) (atom : AtomPat) deriving DecidableEq
def sxException (e : Exception) : Sx :=
  .node "exc" (.cons e.rule.sx (.cons (sxAtomPat e.atom) .nil))
def unException : Sx → Option Exception
  | .node "exc" (.cons r (.cons a .nil)) => do
      let rr ← unRuleId r
      let aa ← unAtomPat a
      some ⟨rr, aa⟩
  | _ => none
@[simp] theorem un_sxException (e : Exception) : unException (sxException e) = some e := by
  cases e with | mk r a => simp [sxException, unException]
@[simp] theorem un_sxList_Exception (xs : List Exception) :
    unSxList unException (sxList sxException xs) = some xs := unSxList_sxList un_sxException xs

/-- Admission map entry `((kind, provenance), admission)` (spec §4.3). -/
abbrev AdmissionEntry := (LeafKind × Provenance) × Admission
def sxAdmEntry (e : AdmissionEntry) : Sx :=
  sxPair (sxPair LeafKind.sx Provenance.sx) Admission.sx e
def unAdmEntry : Sx → Option AdmissionEntry :=
  unSxPair (unSxPair unLeafKind unProvenance) unAdmission
@[simp] theorem un_sxAdmEntry (e : AdmissionEntry) : unAdmEntry (sxAdmEntry e) = some e :=
  unSxPair_sxPair (unSxPair_sxPair un_LeafKind un_Provenance) un_Admission e
@[simp] theorem un_sxList_AdmEntry (xs : List AdmissionEntry) :
    unSxList unAdmEntry (sxList sxAdmEntry xs) = some xs := unSxList_sxList un_sxAdmEntry xs

/-! ## Duplicate-report groups (spec §4.3) -/

/-- A declared duplicate-report group: one measurand cell reported more than once,
each report a distinct leaf. -/
structure DupGroup where mk :: (id : GroupId) (members : List LeafId) deriving DecidableEq
def sxDupGroup (g : DupGroup) : Sx :=
  .node "group" (.cons g.id.sx (.cons (sxList LeafId.sx g.members) .nil))
def unDupGroup : Sx → Option DupGroup
  | .node "group" (.cons i (.cons ms .nil)) => do
      let ii ← unGroupId i
      let mm ← unSxList unLeafId ms
      some ⟨ii, mm⟩
  | _ => none
@[simp] theorem un_sxDupGroup (g : DupGroup) : unDupGroup (sxDupGroup g) = some g := by
  cases g with | mk i ms => simp [sxDupGroup, unDupGroup]

/-! ## Policy-level comparison surface (`lara-syntax@0.3`, grammar App. B.1, B.2)

Presentation-only: the elaborator reads these to expand a `comparison` block, and
nothing here reaches the checker-boundary `Unit`. -/

/-- A policy-level measurand declaration (grammar App. B.1): an arbitrary
declared `TermSort` from the policy's own Σ, and an *optional* polarity — the
`where higher-is-better` clause is `Num`-gated, so a `Num` measurand without one
is legal (it simply cannot key a `ComparisonScheme`). This codec round-trips the
value; the `Num`-gate itself is a well-formedness check, not a codec property,
and is not claimed here. -/
structure Measurand where
  mk :: (id : MeasurandId) (sort : TermSort) (polarity : Option Polarity)
  deriving DecidableEq
def sxMeasurand (m : Measurand) : Sx :=
  .node "meas" (.cons m.id.sx (.cons (sxTermSort m.sort)
    (.cons (sxOpt Polarity.sx m.polarity) .nil)))
def unMeasurand : Sx → Option Measurand
  | .node "meas" (.cons i (.cons s (.cons p .nil))) => do
      let ii ← unMeasurandId i
      let ss ← unTermSort s
      let pp ← unOpt unPolarity p
      some ⟨ii, ss, pp⟩
  | _ => none
@[simp] theorem un_sxMeasurand (m : Measurand) : unMeasurand (sxMeasurand m) = some m := by
  cases m with | mk i s p => simp [sxMeasurand, unMeasurand]
@[simp] theorem un_sxList_Measurand (xs : List Measurand) :
    unSxList unMeasurand (sxList sxMeasurand xs) = some xs := unSxList_sxList un_sxMeasurand xs

/-- A policy-level comparison scheme (grammar App. B.2): the two rules a
`comparison` block expands through, keyed by the pair `(relation, polarity)`. -/
structure ComparisonScheme where
  mk :: (relation : Relation) (polarity : Polarity) (recheck : RuleId) (bridge : RuleId)
  deriving DecidableEq
def sxComparisonScheme (c : ComparisonScheme) : Sx :=
  .node "cscheme" (.cons c.relation.sx (.cons c.polarity.sx
    (.cons c.recheck.sx (.cons c.bridge.sx .nil))))
def unComparisonScheme : Sx → Option ComparisonScheme
  | .node "cscheme" (.cons r (.cons p (.cons rc (.cons br .nil)))) => do
      let rr ← unRelation r
      let pp ← unPolarity p
      let cc ← unRuleId rc
      let bb ← unRuleId br
      some ⟨rr, pp, cc, bb⟩
  | _ => none
@[simp] theorem un_sxComparisonScheme (c : ComparisonScheme) :
    unComparisonScheme (sxComparisonScheme c) = some c := by
  cases c with | mk r p rc br => simp [sxComparisonScheme, unComparisonScheme]
@[simp] theorem un_sxList_ComparisonScheme (xs : List ComparisonScheme) :
    unSxList unComparisonScheme (sxList sxComparisonScheme xs) = some xs :=
  unSxList_sxList un_sxComparisonScheme xs

/-! ## The policy (spec §4) -/

/-- The ten fields of `Lara.AST.Policy`, in order. `sigma` is second, matching
`policySigma`; unlike `measurands` it is *not* presentation-only — the
elaborator copies it verbatim to `unitSigma`, where checker stage 2 enforces it
(rejection class R2). This codec only round-trips it. -/
structure Policy where
  mk ::
  (id : PolicyId) (sigma : Sigma)
  (rules : List Rule) (contraries : List Contrary)
  (exceptions : List Exception) (admission : List AdmissionEntry)
  (theories : List TheoryEntry) (groupMode : GroupConflictMode)
  (measurands : List Measurand) (comparisonSchemes : List ComparisonScheme)
  deriving DecidableEq
def printPolicy (p : Policy) : Sx :=
  .node "policy" (.cons p.id.sx (.cons (sxSigma p.sigma) (.cons (sxList sxRule p.rules)
    (.cons (sxList sxContrary p.contraries) (.cons (sxList sxException p.exceptions)
    (.cons (sxList sxAdmEntry p.admission) (.cons (sxList sxTheoryEntry p.theories)
    (.cons p.groupMode.sx (.cons (sxList sxMeasurand p.measurands)
    (.cons (sxList sxComparisonScheme p.comparisonSchemes) .nil))))))))))
def parsePolicy : Sx → Option Policy
  | .node "policy" (.cons i (.cons sg (.cons rs (.cons cs (.cons es (.cons am (.cons th (.cons gm (.cons ms (.cons sch .nil)))))))))) => do
      let ii ← unPolicyId i
      let gs ← unSigma sg
      let rr ← unSxList unRule rs
      let cc ← unSxList unContrary cs
      let ee ← unSxList unException es
      let aa ← unSxList unAdmEntry am
      let tt ← unSxList unTheoryEntry th
      let gg ← unGroupConflictMode gm
      let mm ← unSxList unMeasurand ms
      let ss ← unSxList unComparisonScheme sch
      some ⟨ii, gs, rr, cc, ee, aa, tt, gg, mm, ss⟩
  | _ => none

/-! ## Positional attacks, argument conclusions, declarations (spec §7, §4.4, §2) -/

inductive Step where
  | premise  : Int → Step
  | question : QuestionId → Step
  deriving DecidableEq
def sxStep : Step → Sx
  | .premise n  => .node "spi" (.cons (.int n) .nil)
  | .question q => .node "sqn" (.cons q.sx .nil)
def unStep : Sx → Option Step
  | .node "spi" (.cons (.int n) .nil) => some (.premise n)
  | .node "sqn" (.cons q .nil)        => do
      let qq ← unQuestionId q
      some (.question qq)
  | _ => none
@[simp] theorem un_sxStep (s : Step) : unStep (sxStep s) = some s := by
  cases s with
  | premise n => rfl
  | question q => simp [sxStep, unStep]
@[simp] theorem un_sxList_Step (xs : List Step) :
    unSxList unStep (sxList sxStep xs) = some xs := unSxList_sxList un_sxStep xs

/-- A position `π` is a path of steps. -/
abbrev Position := List Step

inductive Attack where
  | rebut     : ArgId → ArgId → Attack
  | undercut  : ArgId → ArgId → Position → Attack
  | undermine : ArgId → ArgId → Position → Attack
  deriving DecidableEq
def sxAttack : Attack → Sx
  | .rebut a b       => .node "reb" (.cons a.sx (.cons b.sx .nil))
  | .undercut a b π  => .node "unc" (.cons a.sx (.cons b.sx (.cons (sxList sxStep π) .nil)))
  | .undermine a b π => .node "unm" (.cons a.sx (.cons b.sx (.cons (sxList sxStep π) .nil)))
def unAttack : Sx → Option Attack
  | .node "reb" (.cons a (.cons b .nil)) => do
      let aa ← unArgId a
      let bb ← unArgId b
      some (.rebut aa bb)
  | .node "unc" (.cons a (.cons b (.cons π .nil))) => do
      let aa ← unArgId a
      let bb ← unArgId b
      let pp ← unSxList unStep π
      some (.undercut aa bb pp)
  | .node "unm" (.cons a (.cons b (.cons π .nil))) => do
      let aa ← unArgId a
      let bb ← unArgId b
      let pp ← unSxList unStep π
      some (.undermine aa bb pp)
  | _ => none
@[simp] theorem un_sxAttack (k : Attack) : unAttack (sxAttack k) = some k := by
  cases k with
  | rebut a b => simp [sxAttack, unAttack]
  | undercut a b π => simp [sxAttack, unAttack]
  | undermine a b π => simp [sxAttack, unAttack]

/-! ## Presentation-only attack positions (`lara-syntax@0.3`; grammar §7 AMENDMENT, App. B.5)

`Attack` / `Position` / `Step` above are the **frozen**, Unit-reachable types and
are untouched. `SurfaceAttack` / `SurfaceStep` are the additional presentation
types recording the position *as authored*: `@0.3` admits a dotted segment naming
a rule's premise label (`a2.binding.leaf`) beside the integer spelling
(`a2.1.leaf`), and the printer cannot choose between them because it never sees
the `Policy` where the labels live. `Decl.attack` therefore carries a
`SurfaceAttack`; the elaborator resolves it to the frozen `Attack`. -/

/-- A dotted segment of an attack position exactly as authored. `name` is
deliberately an untyped surface token (like `Sx.str`): which namespace it belongs
to — premise label or question id — is not knowable until the policy is in hand. -/
inductive SurfaceStep where
  | index : Int → SurfaceStep
  | name  : String → SurfaceStep
  deriving DecidableEq
def sxSurfaceStep : SurfaceStep → Sx
  | .index n => .node "ssi" (.cons (.int n) .nil)
  | .name s  => .node "ssn" (.cons (.str s) .nil)
def unSurfaceStep : Sx → Option SurfaceStep
  | .node "ssi" (.cons (.int n) .nil) => some (.index n)
  | .node "ssn" (.cons (.str s) .nil) => some (.name s)
  | _ => none
@[simp] theorem un_sxSurfaceStep (s : SurfaceStep) : unSurfaceStep (sxSurfaceStep s) = some s := by
  cases s <;> rfl
@[simp] theorem un_sxList_SurfaceStep (xs : List SurfaceStep) :
    unSxList unSurfaceStep (sxList sxSurfaceStep xs) = some xs :=
  unSxList_sxList un_sxSurfaceStep xs

/-- A typed positional attack as authored; the three arms mirror `Attack`
one-for-one, with `SurfaceStep` paths in place of resolved `Position`s. -/
inductive SurfaceAttack where
  | rebut     : ArgId → ArgId → SurfaceAttack
  | undercut  : ArgId → ArgId → List SurfaceStep → SurfaceAttack
  | undermine : ArgId → ArgId → List SurfaceStep → SurfaceAttack
  deriving DecidableEq
def sxSurfaceAttack : SurfaceAttack → Sx
  | .rebut a b       => .node "sreb" (.cons a.sx (.cons b.sx .nil))
  | .undercut a b π  => .node "sunc" (.cons a.sx (.cons b.sx (.cons (sxList sxSurfaceStep π) .nil)))
  | .undermine a b π => .node "sunm" (.cons a.sx (.cons b.sx (.cons (sxList sxSurfaceStep π) .nil)))
def unSurfaceAttack : Sx → Option SurfaceAttack
  | .node "sreb" (.cons a (.cons b .nil)) => do
      let aa ← unArgId a
      let bb ← unArgId b
      some (.rebut aa bb)
  | .node "sunc" (.cons a (.cons b (.cons π .nil))) => do
      let aa ← unArgId a
      let bb ← unArgId b
      let pp ← unSxList unSurfaceStep π
      some (.undercut aa bb pp)
  | .node "sunm" (.cons a (.cons b (.cons π .nil))) => do
      let aa ← unArgId a
      let bb ← unArgId b
      let pp ← unSxList unSurfaceStep π
      some (.undermine aa bb pp)
  | _ => none
@[simp] theorem un_sxSurfaceAttack (k : SurfaceAttack) :
    unSurfaceAttack (sxSurfaceAttack k) = some k := by
  cases k with
  | rebut a b => simp [sxSurfaceAttack, unSurfaceAttack]
  | undercut a b π => simp [sxSurfaceAttack, unSurfaceAttack]
  | undermine a b π => simp [sxSurfaceAttack, unSurfaceAttack]

inductive ChallengeTarget where
  | question : QuestionId → ArgId → ChallengeTarget
  | leaf     : LeafId → ChallengeTarget
  deriving DecidableEq
def sxChallengeTarget : ChallengeTarget → Sx
  | .question q u => .node "chq" (.cons q.sx (.cons u.sx .nil))
  | .leaf l       => .node "chl" (.cons l.sx .nil)
def unChallengeTarget : Sx → Option ChallengeTarget
  | .node "chq" (.cons q (.cons u .nil)) => do
      let qq ← unQuestionId q
      let uu ← unArgId u
      some (.question qq uu)
  | .node "chl" (.cons l .nil) => do
      let ll ← unLeafId l
      some (.leaf ll)
  | _ => none
@[simp] theorem un_sxChallengeTarget (t : ChallengeTarget) :
    unChallengeTarget (sxChallengeTarget t) = some t := by
  cases t with
  | question q u => simp [sxChallengeTarget, unChallengeTarget]
  | leaf l => simp [sxChallengeTarget, unChallengeTarget]

inductive ArgConcl where
  | supportsClaim   : PropId → ArgConcl
  | supportsDerived : PropId → ArgConcl
  | challenges      : ChallengeTarget → ArgConcl
  deriving DecidableEq
def sxArgConcl : ArgConcl → Sx
  | .supportsClaim c   => .node "sc" (.cons c.sx .nil)
  | .supportsDerived c => .node "sd" (.cons c.sx .nil)
  | .challenges t      => .node "ch" (.cons (sxChallengeTarget t) .nil)
def unArgConcl : Sx → Option ArgConcl
  | .node "sc" (.cons c .nil) => do
      let cc ← unPropId c
      some (.supportsClaim cc)
  | .node "sd" (.cons c .nil) => do
      let cc ← unPropId c
      some (.supportsDerived cc)
  | .node "ch" (.cons t .nil) => do
      let tt ← unChallengeTarget t
      some (.challenges tt)
  | _ => none
@[simp] theorem un_sxArgConcl (c : ArgConcl) : unArgConcl (sxArgConcl c) = some c := by
  cases c with
  | supportsClaim c => simp [sxArgConcl, unArgConcl]
  | supportsDerived c => simp [sxArgConcl, unArgConcl]
  | challenges t => simp [sxArgConcl, unArgConcl]

inductive ArgInstantiation where
  | explicitTheta (term : SupportTerm)
  | inferTheta (rule : RuleId) (refs : List ArgRef) (discharge : ArgDischarge)
      (obligations : List ObligationId) (assurance : Assurance)
  deriving DecidableEq
def sxArgInstantiation : ArgInstantiation → Sx
  | .explicitTheta term =>
      .node "et" (.cons (sxST term) .nil)
  | .inferTheta rule refs discharge obligations assurance =>
      .node "it" (.cons rule.sx
        (.cons (sxList ArgRef.sx refs)
          (.cons (sxArgDischarge discharge)
            (.cons (sxList ObligationId.sx obligations)
              (.cons (sxAssurance assurance) .nil)))))
def unArgInstantiation : Sx → Option ArgInstantiation
  | .node "et" (.cons term .nil) => do
      let tt ← unST term
      some (.explicitTheta tt)
  | .node "it" (.cons rule (.cons refs (.cons discharge
      (.cons obligations (.cons assurance .nil))))) => do
      let rr ← unRuleId rule
      let rf ← unSxList unArgRef refs
      let dd ← unArgDischarge discharge
      let oo ← unSxList unObligationId obligations
      let aa ← unAssurance assurance
      some (.inferTheta rr rf dd oo aa)
  | _ => none
@[simp] theorem un_sxArgInstantiation (i : ArgInstantiation) :
    unArgInstantiation (sxArgInstantiation i) = some i := by
  cases i with
  | explicitTheta term => simp [sxArgInstantiation, unArgInstantiation]
  | inferTheta rule refs discharge obligations assurance =>
      simp [sxArgInstantiation, unArgInstantiation]

structure Arg where mk ::
  (id : ArgId) (concl : ArgConcl) (instantiation : ArgInstantiation)
  deriving DecidableEq
def sxArg (a : Arg) : Sx :=
  .node "arg" (.cons a.id.sx
    (.cons (sxArgConcl a.concl)
      (.cons (sxArgInstantiation a.instantiation) .nil)))
def unArg : Sx → Option Arg
  | .node "arg" (.cons i (.cons cn (.cons ins .nil))) => do
      let ii ← unArgId i
      let cc ← unArgConcl cn
      let it ← unArgInstantiation ins
      some ⟨ii, cc, it⟩
  | _ => none
@[simp] theorem un_sxArg (a : Arg) : unArg (sxArg a) = some a := by
  cases a with | mk i c ins => simp [sxArg, unArg]

/-! ## Comparison blocks (`lara-syntax@0.3`, grammar App. B.3)

Presentation-only: the elaborator expands a `comparison` into ordinary `claim` and
`arg` declarations before the checker anchor exists, and a `comparison` round-trips
as a `comparison`, never as its expansion. -/

/-- The `claims` sub-block of a `comparison`: the parts of the generated sub-claim
a machine cannot invent. `nlRaw` is the `nl` string **raw, exactly as authored** —
`{cell l}` directives unexpanded and `{{`/`}}` escapes unconverted (App. B.6) — so
the codec returns the authored bytes and the round-trip holds on the spelling. -/
structure ComparisonClaim where
  mk :: (id : PropId) (nlRaw : String) (binding : Binding)
  deriving DecidableEq
def sxComparisonClaim (c : ComparisonClaim) : Sx :=
  .node "cclaim" (.cons c.id.sx (.cons (.str c.nlRaw) (.cons (sxBinding c.binding) .nil)))
def unComparisonClaim : Sx → Option ComparisonClaim
  | .node "cclaim" (.cons i (.cons (.str nl) (.cons bd .nil))) => do
      let ii ← unPropId i
      let bb ← unBinding bd
      some ⟨ii, nl, bb⟩
  | _ => none
@[simp] theorem un_sxComparisonClaim (c : ComparisonClaim) :
    unComparisonClaim (sxComparisonClaim c) = some c := by
  cases c with | mk i nl b => simp [sxComparisonClaim, unComparisonClaim]

/-- A `comparison` block (grammar App. B.3). `conclusion` is the authored 2-ary
system pair `pred(S, B)`; the elaborator forms the scheme's 4-ary conclusion by
adding `measurand` (Q) and `dataset` (D). -/
structure Comparison where
  mk ::
  (conclusion : Atom) (measurand : MeasurandId) (dataset : DatasetId) (relation : Relation)
  (recheckArg : ArgId) (bridgeArg : ArgId)
  (result : LeafId) (baseline : LeafId) (binding : LeafId)
  (claim : ComparisonClaim) (supports : Option PropId)
  deriving DecidableEq
def sxComparison (c : Comparison) : Sx :=
  .node "cmp" (.cons (sxAtom c.conclusion) (.cons c.measurand.sx (.cons c.dataset.sx
    (.cons c.relation.sx (.cons c.recheckArg.sx (.cons c.bridgeArg.sx
    (.cons c.result.sx (.cons c.baseline.sx (.cons c.binding.sx
    (.cons (sxComparisonClaim c.claim) (.cons (sxOpt PropId.sx c.supports) .nil)))))))))))
def unComparison : Sx → Option Comparison
  | .node "cmp" (.cons cn (.cons me (.cons da (.cons rl (.cons rc (.cons br
      (.cons rs (.cons bl (.cons bd (.cons cl (.cons sp .nil))))))))))) => do
      let cc ← unAtom cn
      let mm ← unMeasurandId me
      let dd ← unDatasetId da
      let ll ← unRelation rl
      let rr ← unArgId rc
      let bb ← unArgId br
      let ss ← unLeafId rs
      let aa ← unLeafId bl
      let gg ← unLeafId bd
      let kk ← unComparisonClaim cl
      let pp ← unOpt unPropId sp
      some ⟨cc, mm, dd, ll, rr, bb, ss, aa, gg, kk, pp⟩
  | _ => none
@[simp] theorem un_sxComparison (c : Comparison) : unComparison (sxComparison c) = some c := by
  cases c with
  | mk cn me da rl rc br rs bl bd cl sp => simp [sxComparison, unComparison]

inductive Decl where
  | leaf       : Leaf → Decl
  | claim      : Claim → Decl
  | arg        : Arg → Decl
  /-- An attack **as authored** (grammar §7 AMENDMENT): a `SurfaceAttack`, which
  the elaborator resolves to the frozen `Attack` once the policy is in hand. -/
  | attack     : SurfaceAttack → Decl
  | status     : PropId → Decl
  | group      : DupGroup → Decl
  | comparison : Comparison → Decl
  deriving DecidableEq
def sxDecl : Decl → Sx
  | .leaf l       => .node "dl" (.cons (sxLeaf l) .nil)
  | .claim c      => .node "dc" (.cons (sxClaim c) .nil)
  | .arg a        => .node "da" (.cons (sxArg a) .nil)
  | .attack k     => .node "dk" (.cons (sxSurfaceAttack k) .nil)
  | .status p     => .node "ds" (.cons p.sx .nil)
  | .group g      => .node "dg" (.cons (sxDupGroup g) .nil)
  | .comparison c => .node "dm" (.cons (sxComparison c) .nil)
def unDecl : Sx → Option Decl
  | .node "dl" (.cons l .nil) => do let ll ← unLeaf l;   some (.leaf ll)
  | .node "dc" (.cons c .nil) => do let cc ← unClaim c;  some (.claim cc)
  | .node "da" (.cons a .nil) => do let aa ← unArg a;    some (.arg aa)
  | .node "dk" (.cons k .nil) => do let kk ← unSurfaceAttack k; some (.attack kk)
  | .node "ds" (.cons p .nil) => do let pp ← unPropId p; some (.status pp)
  | .node "dg" (.cons g .nil) => do let gg ← unDupGroup g; some (.group gg)
  | .node "dm" (.cons c .nil) => do let cc ← unComparison c; some (.comparison cc)
  | _ => none
@[simp] theorem un_sxDecl (d : Decl) : unDecl (sxDecl d) = some d := by
  cases d with
  | leaf l => simp [sxDecl, unDecl]
  | claim c => simp [sxDecl, unDecl]
  | arg a => simp [sxDecl, unDecl]
  | attack k => simp [sxDecl, unDecl]
  | status p => simp [sxDecl, unDecl]
  | group g => simp [sxDecl, unDecl]
  | comparison c => simp [sxDecl, unDecl]
@[simp] theorem un_sxList_Decl (xs : List Decl) :
    unSxList unDecl (sxList sxDecl xs) = some xs := unSxList_sxList un_sxDecl xs

/-! ## Programs (spec §2, §4.4) -/

/-- Backend-registry entry `(β, version)`. -/
abbrev BackendEntry := BackendId × String
def sxBackend (e : BackendEntry) : Sx := sxPair BackendId.sx sxStr e
def unBackend : Sx → Option BackendEntry := unSxPair unBackendId unStr
@[simp] theorem un_sxBackend (e : BackendEntry) : unBackend (sxBackend e) = some e :=
  unSxPair_sxPair un_BackendId unStr_sxStr e
@[simp] theorem un_sxList_Backend (xs : List BackendEntry) :
    unSxList unBackend (sxList sxBackend xs) = some xs := unSxList_sxList un_sxBackend xs

/-! `lara-syntax@0.4` value bindings (grammar Appendix C) are a
presentation-only ordered table. The elaborator consumes them before comparison
expansion; the structured codec preserves their authored shape. -/
structure ValueBinding where
  mk :: (name : ValueName) (term : Term)
  deriving DecidableEq
def sxValueBinding (b : ValueBinding) : Sx :=
  .node "value-binding" (.cons b.name.sx (.cons (sxTerm b.term) .nil))
def unValueBinding : Sx → Option ValueBinding
  | .node "value-binding" (.cons nm (.cons tm .nil)) => do
      let nn ← unValueName nm
      let tt ← unTerm tm
      some ⟨nn, tt⟩
  | _ => none
@[simp] theorem un_sxValueBinding (b : ValueBinding) :
    unValueBinding (sxValueBinding b) = some b := by
  cases b with | mk n t => simp [sxValueBinding, unValueBinding]
@[simp] theorem un_sxList_ValueBinding (xs : List ValueBinding) :
    unSxList unValueBinding (sxList sxValueBinding xs) = some xs :=
  unSxList_sxList un_sxValueBinding xs

structure Program where
  mk ::
  (artifact : String) (digest : Digest) (policy : PolicyId)
  (backends : List BackendEntry) (valueBindings : List ValueBinding) (decls : List Decl)
  deriving DecidableEq
def printProgram (p : Program) : Sx :=
  .node "program" (.cons (.str p.artifact) (.cons p.digest.sx (.cons p.policy.sx
    (.cons (sxList sxBackend p.backends) (.cons (sxList sxValueBinding p.valueBindings)
    (.cons (sxList sxDecl p.decls) .nil))))))
def parseProgram : Sx → Option Program
  | .node "program" (.cons (.str ar) (.cons dg (.cons pl
      (.cons bk (.cons vb (.cons ds .nil)))))) => do
      let dd ← unDigest dg
      let pp ← unPolicyId pl
      let bb ← unSxList unBackend bk
      let vv ← unSxList unValueBinding vb
      let dcs ← unSxList unDecl ds
      some ⟨ar, dd, pp, bb, vv, dcs⟩
  | _ => none

/-! ## The round-trip theorems (spec §9 result 12)

`parse ∘ print = id` for the two top-level presentation categories. Both close by
`simp` because every field codec's round-trip is an `@[simp]` lemma. -/

theorem parse_printProgram (p : Program) : parseProgram (printProgram p) = some p := by
  cases p with | mk ar dg pl bk vb ds => simp [printProgram, parseProgram]

theorem parse_printPolicy (q : Policy) : parsePolicy (printPolicy q) = some q := by
  cases q with | mk i sg rs cs es am th gm ms sch => simp [printPolicy, parsePolicy]

end Lara.Presentation
