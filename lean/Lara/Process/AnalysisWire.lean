import Lara.Process.Analysis
import Lara.Process.SourceAuditWire
import Lara.Process.FamilyWire
import Lara.Process.SourceResultWire

/-!
Canonical codecs for the P3 analyses (issue #22, stage P3).

One closed `Tag` table with the five customary laws; every P3 record and result
type then has an exact-arity encoder/decoder over the Driver S-expression
carrier. Process identity tables (`Process.Wire.Names`), claim/witness indices,
event stamps, queries, completions and slot/choice identities reuse the landed
`SourceWire` / `InquiryProcessWire` / `Process.Wire` / `Family.Wire` spellings
and helpers — no second convention is introduced for process names, statuses or
slots. Slots and choice identities are canonical naturals; public statuses reuse
`ResultWire.encodePublicStatus`. Every accepted wire value re-encodes to the
bytes it came from, and type-level data round-trips and is injective; the only
context needed is the `Names` table (with its `UniqueNames`/bound hypotheses),
exactly as for the landed codecs.
-/

namespace Lara.Process.Analysis.AnalysisWire

open Lara.Driver (Sx)
open Lara.Process
open Lara.Process.Source
open Lara.Process.Wire (Spelling ProfileSpec)

/-- A codec-local type alias for the only contextual parameter. -/
abbrev Names := Process.Wire.Names

abbrev UniqueNames := InquiryProcessWire.UniqueNames
abbrev StampedWellNamed := InquiryProcessWire.StampedWellNamed
abbrev QueryWellNamed := InquiryProcessWire.QueryWellNamed

/-! ### The closed tag table -/

inductive Tag where
  | observable | target
  | obsStatus | obsAudit | tgtStatus | tgtAudit
  | literal | slotEq | slotNe | litPresent | litAbsent | litBefore | litFormula | litNotFormula
  | row | stabilityResult | sensitivityResult | deletion | minimalSet | assumptionResult
  | profile | guarantee | acceptance
  deriving DecidableEq, Repr

def Tag.text : Tag → String
  | .observable => "observable" | .target => "target"
  | .obsStatus => "status-obs" | .obsAudit => "audit-obs"
  | .tgtStatus => "status-target" | .tgtAudit => "audit-target"
  | .literal => "literal" | .slotEq => "slot-eq" | .slotNe => "slot-ne"
  | .litPresent => "lit-present" | .litAbsent => "lit-absent" | .litBefore => "lit-before"
  | .litFormula => "lit-formula" | .litNotFormula => "lit-not-formula"
  | .row => "row" | .stabilityResult => "stability-result"
  | .sensitivityResult => "sensitivity-result" | .deletion => "deletion"
  | .minimalSet => "minimal-set" | .assumptionResult => "assumption-result"
  | .profile => "profile" | .guarantee => "guarantee" | .acceptance => "acceptance"

def Tag.all : List Tag :=
  [.observable, .target, .obsStatus, .obsAudit, .tgtStatus, .tgtAudit, .literal, .slotEq, .slotNe,
   .litPresent, .litAbsent, .litBefore, .litFormula, .litNotFormula, .row, .stabilityResult,
   .sensitivityResult, .deletion, .minimalSet, .assumptionResult, .profile, .guarantee,
   .acceptance]

def Tag.spelling : Spelling Tag := ⟨Tag.all, Tag.text⟩

def Tag.parse (s : String) : Option Tag := Tag.spelling.parse s

theorem Tag.spelling_complete (tag : Tag) : tag ∈ Tag.spelling.all := by cases tag <;> decide

theorem Tag.spelling_nodup : (Tag.spelling.all.map Tag.spelling.text).Nodup := by decide

@[simp] theorem Tag.parse_text (tag : Tag) : Tag.parse tag.text = some tag :=
  Tag.spelling.parse_text Tag.spelling_complete Tag.spelling_nodup tag

theorem Tag.parse_some {text : String} {tag : Tag} (h : Tag.parse text = some tag) :
    tag.text = text := Tag.spelling.parse_some h

theorem Tag.text_injective : Function.Injective Tag.text :=
  Tag.spelling.text_injective Tag.spelling_complete Tag.spelling_nodup

/-- A tagged list in this module's own closed vocabulary. -/
def tagged (tag : Tag) (args : List Sx) : Sx := .list (.atom tag.text :: args)

private theorem except_toOption_some {e : Except ε α} {a : α} :
    e.toOption = some a ↔ e = .ok a := by
  cases e <;> simp [Except.toOption]

private theorem bind_some_iff {x : Option α} {f : α → Option β} {b : β} :
    (x >>= f) = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp

private theorem pure_some_iff {a b : α} : (pure a : Option α) = some b ↔ a = b := by
  constructor
  · exact Option.some.inj
  · intro h; cases h; rfl

private theorem injective_on_of_roundtrip (encode : α → Sx) (decode : Sx → Option α)
    (p : α → Prop) (roundtrip : ∀ a, p a → decode (encode a) = some a)
    {a b : α} (ha : p a) (hb : p b) (equal : encode a = encode b) : a = b := by
  have h := congrArg decode equal
  simpa only [roundtrip a ha, roundtrip b hb, Option.some.injEq] using h

/-! ### Composite helpers -/

def encodeList (encode : α → Sx) (xs : List α) : Sx := .list (xs.map encode)

def decodeList (decode : Sx → Option α) : Sx → Option (List α)
  | .list xs => Source.Wire.decodeList decode xs
  | _ => none

@[simp] theorem decode_encodeList (encode : α → Sx) (decode : Sx → Option α)
    (h : ∀ a, decode (encode a) = some a) (xs : List α) :
    decodeList decode (encodeList encode xs) = some xs := by
  simp [decodeList, encodeList, Source.Wire.decodeList_map, h]

universe u v

def encodePair {α : Type u} {β : Type v} (ea : α → Sx) (eb : β → Sx) (p : α × β) : Sx :=
  .list [ea p.1, eb p.2]

def decodePair {α : Type u} {β : Type v} (da : Sx → Option α) (db : Sx → Option β) :
    Sx → Option (α × β)
  | .list [a, b] => Option.bind (da a) fun x => Option.map (fun y => (x, y)) (db b)
  | _ => none

@[simp] theorem decode_encodePair {α : Type u} {β : Type v} (ea : α → Sx) (eb : β → Sx)
    (da : Sx → Option α) (db : Sx → Option β)
    (ha : ∀ a, da (ea a) = some a) (hb : ∀ b, db (eb b) = some b) (p : α × β) :
    decodePair da db (encodePair ea eb p) = some p := by
  obtain ⟨a, b⟩ := p
  simp [encodePair, decodePair, ha, hb]

theorem decode_encodePair_of {α : Type u} {β : Type v} (ea : α → Sx) (eb : β → Sx)
    (da : Sx → Option α) (db : Sx → Option β) (pa : α → Prop) (pb : β → Prop)
    (ha : ∀ a, pa a → da (ea a) = some a) (hb : ∀ b, pb b → db (eb b) = some b)
    (p : α × β) (hp : pa p.1 ∧ pb p.2) :
    decodePair da db (encodePair ea eb p) = some p := by
  obtain ⟨a, b⟩ := p
  obtain ⟨hpa, hpb⟩ := hp
  simp [encodePair, decodePair, ha a hpa, hb b hpb]

def encodeOpt (encode : α → Sx) : Option α → Sx
  | none => .list []
  | some a => .list [encode a]

def decodeOpt (decode : Sx → Option α) : Sx → Option (Option α)
  | .list [] => some none
  | .list [a] => (decode a).map some
  | _ => none

@[simp] theorem decode_encodeOpt (encode : α → Sx) (decode : Sx → Option α)
    (h : ∀ a, decode (encode a) = some a) (o : Option α) :
    decodeOpt decode (encodeOpt encode o) = some o := by
  cases o <;> simp [encodeOpt, decodeOpt, h]

theorem decode_encodeOpt_of (encode : α → Sx) (decode : Sx → Option α) (p : α → Prop)
    (h : ∀ a, p a → decode (encode a) = some a) (o : Option α) (ho : ∀ a ∈ o, p a) :
    decodeOpt decode (encodeOpt encode o) = some o := by
  cases o with
  | none => rfl
  | some a => simp [encodeOpt, decodeOpt, h a (ho a (by simp))]

abbrev encodeBool := AuditWire.encodeBool
abbrev decodeBool := AuditWire.decodeBool
abbrev encodeStamped := AuditWire.encodeStamped
abbrev decodeStamped := AuditWire.decodeStamped
abbrev encodeClaimId := AuditWire.encodeClaimId
abbrev decodeClaimId := AuditWire.decodeClaimId
abbrev encodeWitnessId := AuditWire.encodeWitnessId
abbrev decodeWitnessId := AuditWire.decodeWitnessId
abbrev encodeCompletion := Family.Wire.encodeCompletion
abbrev decodeCompletion := Family.Wire.decodeCompletion
abbrev CompletionWellNamed := Family.Wire.CompletionWellNamed
abbrev encodeSlotId := Family.Wire.encodeSlotId
abbrev decodeSlotId := Family.Wire.decodeSlotId
abbrev encodeChoiceId := Family.Wire.encodeChoiceId
abbrev decodeChoiceId := Family.Wire.decodeChoiceId
abbrev encodePublicStatus := ResultWire.encodePublicStatus
abbrev decodePublicStatus := ResultWire.decodePublicStatus

/-- The duplicate-free list round trip for a well-named predicate. -/
theorem decodeList_map_of (encode : α → Sx) (decode : Sx → Option α) (p : α → Prop)
    (roundtrip : ∀ a, p a → decode (encode a) = some a) (values : List α)
    (valid : ∀ a ∈ values, p a) :
    Source.Wire.decodeList decode (values.map encode) = some values := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
      have ha := roundtrip a (valid a (by simp))
      have hrest := ih (fun x hx => valid x (by simp [hx]))
      simp [Source.Wire.decodeList, ha, hrest]

theorem decode_encodeList_of (encode : α → Sx) (decode : Sx → Option α) (p : α → Prop)
    (roundtrip : ∀ a, p a → decode (encode a) = some a) (values : List α)
    (valid : ∀ a ∈ values, p a) : decodeList decode (encodeList encode values) = some values := by
  unfold decodeList encodeList
  exact decodeList_map_of encode decode p roundtrip values valid

/-! ### Profile record -/

def encodeWords {α : Type} (sp : Spelling α) (l : List α) : Sx :=
  .list (l.map fun a => .atom (sp.text a))

def decodeWords {α : Type} (sp : Spelling α) : Sx → Option (List α)
  | .list xs => Source.Wire.decodeList (fun w => match w with | .atom s => sp.parse s | _ => none) xs
  | _ => none

theorem decode_encodeWords {α : Type} (sp : Spelling α)
    (complete : ∀ a, a ∈ sp.all) (nodup : (sp.all.map sp.text).Nodup) (l : List α) :
    decodeWords sp (encodeWords sp l) = some l := by
  have h : ∀ a, (fun w : Sx => match w with | .atom s => sp.parse s | _ => none)
      (.atom (sp.text a)) = some a := fun a => sp.parse_text complete nodup a
  simpa [decodeWords, encodeWords] using Source.Wire.decodeList_map _ _ h l

def encodeGuaranteeSpec (cls : GuaranteeClass) (num den : Nat) : Sx :=
  tagged .guarantee [.atom (Process.Wire.GuaranteeClass.spelling.text cls),
    Process.Wire.encodeNat num, Process.Wire.encodeNat den]

def decodeGuaranteeSpec : Sx → Option (GuaranteeClass × Nat × Nat)
  | .list (.atom t :: [.atom c, a, b]) =>
      if t = (Tag.guarantee).text then do
        return (← Process.Wire.GuaranteeClass.spelling.parse c,
          ← (Process.Wire.decodeNat a).toOption, ← (Process.Wire.decodeNat b).toOption)
      else none
  | _ => none

theorem decode_encodeGuaranteeSpec (cls : GuaranteeClass) (num den : Nat) :
    decodeGuaranteeSpec (encodeGuaranteeSpec cls num den) = some (cls, num, den) := by
  have hp : Process.Wire.GuaranteeClass.spelling.parse
      (Process.Wire.GuaranteeClass.spelling.text cls) = some cls :=
    Process.Wire.GuaranteeClass.spelling.parse_text
      Process.Wire.GuaranteeClass.spelling_complete Process.Wire.GuaranteeClass.spelling_nodup cls
  simp [encodeGuaranteeSpec, decodeGuaranteeSpec, tagged, hp,
    InquiryProcessWire.decode_encodeNat]

def encodeAcceptanceSpec (a : Acceptance) : Sx :=
  tagged .acceptance [.atom (Process.Wire.Acceptance.spelling.text a)]

def decodeAcceptanceSpec : Sx → Option Acceptance
  | .list (.atom t :: [a]) =>
      if t = (Tag.acceptance).text then
        (match a with | .atom s => Process.Wire.Acceptance.spelling.parse s | _ => none)
      else none
  | _ => none

theorem decode_encodeAcceptanceSpec (a : Acceptance) :
    decodeAcceptanceSpec (encodeAcceptanceSpec a) = some a := by
  have hp := Process.Wire.Acceptance.spelling.parse_text
    Process.Wire.Acceptance.spelling_complete Process.Wire.Acceptance.spelling_nodup a
  cases a; simp [encodeAcceptanceSpec, decodeAcceptanceSpec, tagged, hp]

def encodeProfileSpec (s : ProfileSpec) : Sx :=
  match s with
  | ⟨admissible, accepts, guarantee, num, den, probes, acceptance⟩ =>
    tagged .profile [encodeWords Process.Wire.EvidenceKind.spelling admissible,
      encodeWords Process.Wire.CoverageKind.spelling accepts,
      encodeGuaranteeSpec guarantee num den,
      encodeWords Process.Wire.ErrorKind.spelling probes,
      encodeAcceptanceSpec acceptance]

def decodeProfileSpecRaw : Sx → Option ProfileSpec
  | .list (.atom t :: [adm, acc, gu, pr, ac]) =>
      if t = (Tag.profile).text then
        (match decodeGuaranteeSpec gu with
         | some (cls, num, den) => do
             return ⟨← decodeWords Process.Wire.EvidenceKind.spelling adm,
               ← decodeWords Process.Wire.CoverageKind.spelling acc, cls, num, den,
               ← decodeWords Process.Wire.ErrorKind.spelling pr, ← decodeAcceptanceSpec ac⟩
         | none => none)
      else none
  | _ => none

def decodeProfileSpec (wire : Sx) : Option ProfileSpec :=
  Source.Wire.canonical encodeProfileSpec decodeProfileSpecRaw wire

theorem decode_encodeProfileSpec (s : ProfileSpec) :
    decodeProfileSpec (encodeProfileSpec s) = some s := by
  have h : ∀ a : ProfileSpec, decodeProfileSpecRaw (encodeProfileSpec a) = some a := by
    intro a
    obtain ⟨admissible, accepts, guarantee, num, den, probes, acceptance⟩ := a
    have e1 : decodeWords Process.Wire.EvidenceKind.spelling
        (encodeWords Process.Wire.EvidenceKind.spelling admissible) = some admissible :=
      decode_encodeWords _ Process.Wire.EvidenceKind.spelling_complete
        Process.Wire.EvidenceKind.spelling_nodup admissible
    have e2 : decodeWords Process.Wire.CoverageKind.spelling
        (encodeWords Process.Wire.CoverageKind.spelling accepts) = some accepts :=
      decode_encodeWords _ Process.Wire.CoverageKind.spelling_complete
        Process.Wire.CoverageKind.spelling_nodup accepts
    have e3 : decodeWords Process.Wire.ErrorKind.spelling
        (encodeWords Process.Wire.ErrorKind.spelling probes) = some probes :=
      decode_encodeWords _ Process.Wire.ErrorKind.spelling_complete
        Process.Wire.ErrorKind.spelling_nodup probes
    simp only [encodeProfileSpec, tagged, decodeProfileSpecRaw]
    simp [e1, e2, e3, decode_encodeGuaranteeSpec, decode_encodeAcceptanceSpec]
  exact Source.Wire.canonical_roundtrip encodeProfileSpec decodeProfileSpecRaw h s

theorem decodeProfileSpec_canonical {wire : Sx} {value : ProfileSpec}
    (h : decodeProfileSpec wire = some value) : encodeProfileSpec value = wire :=
  Source.Wire.canonical_sound _ _ h

theorem encodeProfileSpec_injective : Function.Injective encodeProfileSpec :=
  Source.Wire.injective_of_roundtrip _ _ decode_encodeProfileSpec

/-! ### Observable and target specs -/

inductive ObservableSpec where
  | status (claim : ClaimId)
  | audit (claim : ClaimId) (witness : WitnessId) (profile : ProfileSpec)
  deriving DecidableEq

inductive TargetSpec where
  | status (claim : ClaimId) (expected : Driver.PublicStatus)
  | audit (claim : ClaimId) (witness : WitnessId) (profile : ProfileSpec)
  deriving DecidableEq

def ObservableSpec.toObservable : ObservableSpec → Observable
  | .status claim => .status claim
  | .audit claim witness profile => .audit claim witness profile.toProfile

def TargetSpec.toTarget : TargetSpec → Target
  | .status claim expected => .status claim expected
  | .audit claim witness profile => .audit claim witness profile.toProfile

def ObservableWellNamed (n : Names) : ObservableSpec → Prop
  | .status claim => claim.index < n.claim.length
  | .audit claim witness _ =>
      claim.index < n.claim.length ∧ witness.index < n.witness.length

def TargetWellNamed (n : Names) : TargetSpec → Prop
  | .status claim _ => claim.index < n.claim.length
  | .audit claim witness _ =>
      claim.index < n.claim.length ∧ witness.index < n.witness.length

def encodeObservableSpec (n : Names) : ObservableSpec → Sx
  | .status claim => tagged .observable [tagged .obsStatus [encodeClaimId n claim]]
  | .audit claim witness profile =>
      tagged .observable [tagged .obsAudit [encodeClaimId n claim, encodeWitnessId n witness,
        encodeProfileSpec profile]]

def decodeObservableSpecRaw (n : Names) : Sx → Option ObservableSpec
  | .list (.atom t :: [.list (.atom t' :: args)]) =>
      if t = (Tag.observable).text then
        match Tag.parse t' with
        | some .obsStatus =>
            (match args with | [c] => (decodeClaimId n c).map ObservableSpec.status | _ => none)
        | some .obsAudit =>
            (match args with
             | [c, w, p] => (match decodeProfileSpec p with
                 | some profile => (match decodeClaimId n c, decodeWitnessId n w with
                     | some claim, some witness => some (.audit claim witness profile)
                     | _, _ => none)
                 | none => none)
             | _ => none)
        | _ => none
      else none
  | _ => none

/-- The canonical decoder: only the unique canonical spelling is retained, so
untrusted bytes decode to a value exactly when they are that value's bytes. -/
def decodeObservableSpec (n : Names) (wire : Sx) : Option ObservableSpec :=
  Source.Wire.canonical (encodeObservableSpec n) (decodeObservableSpecRaw n) wire

theorem decodeObservableSpec_canonical {n : Names} {wire : Sx} {value : ObservableSpec}
    (h : decodeObservableSpec n wire = some value) : encodeObservableSpec n value = wire :=
  Source.Wire.canonical_sound _ _ h

theorem decode_encodeObservableSpec (n : Names) (unique : UniqueNames n) (value : ObservableSpec)
    (valid : ObservableWellNamed n value) :
    decodeObservableSpec n (encodeObservableSpec n value) = some value := by
  have hraw : decodeObservableSpecRaw n (encodeObservableSpec n value) = some value := by
    cases value with
    | status claim =>
        have hc := AuditWire.decode_encodeClaimId n unique claim valid
        simp [encodeObservableSpec, decodeObservableSpecRaw, tagged, Tag.parse_text, hc]
    | audit claim witness profile =>
        obtain ⟨hc, hw⟩ := valid
        have hc' := AuditWire.decode_encodeClaimId n unique claim hc
        have hw' := AuditWire.decode_encodeWitnessId n unique witness hw
        have hp := decode_encodeProfileSpec profile
        simp [encodeObservableSpec, decodeObservableSpecRaw, tagged, Tag.parse_text, hc', hw', hp]
  unfold decodeObservableSpec Source.Wire.canonical
  rw [hraw]
  simp

def encodeTargetSpec (n : Names) : TargetSpec → Sx
  | .status claim expected =>
      tagged .target [tagged .tgtStatus [encodeClaimId n claim, encodePublicStatus expected]]
  | .audit claim witness profile =>
      tagged .target [tagged .tgtAudit [encodeClaimId n claim, encodeWitnessId n witness,
        encodeProfileSpec profile]]

def decodeTargetSpecRaw (n : Names) : Sx → Option TargetSpec
  | .list (.atom t :: [.list (.atom t' :: args)]) =>
      if t = (Tag.target).text then
        match Tag.parse t' with
        | some .tgtStatus =>
            (match args with
             | [c, s] => (match decodePublicStatus s with
                 | some expected => (decodeClaimId n c).map (TargetSpec.status · expected)
                 | none => none)
             | _ => none)
        | some .tgtAudit =>
            (match args with
             | [c, w, p] => (match decodeProfileSpec p with
                 | some profile => (match decodeClaimId n c, decodeWitnessId n w with
                     | some claim, some witness => some (.audit claim witness profile)
                     | _, _ => none)
                 | none => none)
             | _ => none)
        | _ => none
      else none
  | _ => none

/-- The canonical decoder for target specs, mirroring `decodeObservableSpec`. -/
def decodeTargetSpec (n : Names) (wire : Sx) : Option TargetSpec :=
  Source.Wire.canonical (encodeTargetSpec n) (decodeTargetSpecRaw n) wire

theorem decodeTargetSpec_canonical {n : Names} {wire : Sx} {value : TargetSpec}
    (h : decodeTargetSpec n wire = some value) : encodeTargetSpec n value = wire :=
  Source.Wire.canonical_sound _ _ h

theorem decode_encodeTargetSpec (n : Names) (unique : UniqueNames n) (value : TargetSpec)
    (valid : TargetWellNamed n value) :
    decodeTargetSpec n (encodeTargetSpec n value) = some value := by
  have hraw : decodeTargetSpecRaw n (encodeTargetSpec n value) = some value := by
    cases value with
    | status claim expected =>
        have hc := AuditWire.decode_encodeClaimId n unique claim valid
        simp [encodeTargetSpec, decodeTargetSpecRaw, tagged, Tag.parse_text, hc,
          ResultWire.decode_encodePublicStatus]
    | audit claim witness profile =>
        obtain ⟨hc, hw⟩ := valid
        have hc' := AuditWire.decode_encodeClaimId n unique claim hc
        have hw' := AuditWire.decode_encodeWitnessId n unique witness hw
        have hp := decode_encodeProfileSpec profile
        simp [encodeTargetSpec, decodeTargetSpecRaw, tagged, Tag.parse_text, hc', hw', hp]
  unfold decodeTargetSpec Source.Wire.canonical
  rw [hraw]
  simp

theorem encodeObservableSpec_injective (n : Names) (unique : UniqueNames n)
    {a b : ObservableSpec} (ha : ObservableWellNamed n a) (hb : ObservableWellNamed n b)
    (h : encodeObservableSpec n a = encodeObservableSpec n b) : a = b :=
  injective_on_of_roundtrip _ _ _ (decode_encodeObservableSpec n unique) ha hb h

theorem encodeTargetSpec_injective (n : Names) (unique : UniqueNames n)
    {a b : TargetSpec} (ha : TargetWellNamed n a) (hb : TargetWellNamed n b)
    (h : encodeTargetSpec n a = encodeTargetSpec n b) : a = b :=
  injective_on_of_roundtrip _ _ _ (decode_encodeTargetSpec n unique) ha hb h

/-! ### Literal catalog -/

def LiteralWellNamed (n : Names) : Literal → Prop
  | .slotEq _ _ => True
  | .slotNe _ _ => True
  | .present e => StampedWellNamed n e
  | .absent e => StampedWellNamed n e
  | .before a b => StampedWellNamed n a ∧ StampedWellNamed n b
  | .formula q => QueryWellNamed n q
  | .notFormula q => QueryWellNamed n q

def encodeLiteral (n : Names) : Literal → Sx
  | .slotEq slot choice => tagged .literal [tagged .slotEq [encodeSlotId slot, encodeChoiceId choice]]
  | .slotNe slot choice => tagged .literal [tagged .slotNe [encodeSlotId slot, encodeChoiceId choice]]
  | .present e => tagged .literal [tagged .litPresent [encodeStamped n e]]
  | .absent e => tagged .literal [tagged .litAbsent [encodeStamped n e]]
  | .before a b => tagged .literal [tagged .litBefore [encodeStamped n a, encodeStamped n b]]
  | .formula q => tagged .literal [tagged .litFormula [Process.Wire.encodeQuery n q]]
  | .notFormula q => tagged .literal [tagged .litNotFormula [Process.Wire.encodeQuery n q]]

def decodeLiteralRaw (n : Names) : Sx → Option Literal
  | .list (.atom t :: [.list (.atom t' :: args)]) =>
      if t = (Tag.literal).text then
        match Tag.parse t' with
        | some .slotEq =>
            (match args with
             | [s, c] => (match decodeSlotId s, decodeChoiceId c with
                 | some slot, some choice => some (.slotEq slot choice) | _, _ => none)
             | _ => none)
        | some .slotNe =>
            (match args with
             | [s, c] => (match decodeSlotId s, decodeChoiceId c with
                 | some slot, some choice => some (.slotNe slot choice) | _, _ => none)
             | _ => none)
        | some .litPresent =>
            (match args with | [e] => (decodeStamped n e).map Literal.present | _ => none)
        | some .litAbsent =>
            (match args with | [e] => (decodeStamped n e).map Literal.absent | _ => none)
        | some .litBefore =>
            (match args with
             | [a, b] => (match decodeStamped n a, decodeStamped n b with
                 | some x, some y => some (.before x y) | _, _ => none)
             | _ => none)
        | some .litFormula =>
            (match args with
             | [q] => (Process.Wire.decodeQuery n q).toOption.map Literal.formula | _ => none)
        | some .litNotFormula =>
            (match args with
             | [q] => (Process.Wire.decodeQuery n q).toOption.map Literal.notFormula | _ => none)
        | _ => none
      else none
  | _ => none

/-- The canonical literal decoder. -/
def decodeLiteral (n : Names) (wire : Sx) : Option Literal :=
  Source.Wire.canonical (encodeLiteral n) (decodeLiteralRaw n) wire

theorem decodeLiteral_canonical {n : Names} {wire : Sx} {value : Literal}
    (h : decodeLiteral n wire = some value) : encodeLiteral n value = wire :=
  Source.Wire.canonical_sound _ _ h

theorem decode_encodeLiteral (n : Names) (unique : UniqueNames n) (value : Literal)
    (valid : LiteralWellNamed n value) :
    decodeLiteral n (encodeLiteral n value) = some value := by
  have hraw : decodeLiteralRaw n (encodeLiteral n value) = some value := by
    cases value with
    | slotEq slot choice => simp [encodeLiteral, decodeLiteralRaw, tagged, Tag.parse_text]
    | slotNe slot choice => simp [encodeLiteral, decodeLiteralRaw, tagged, Tag.parse_text]
    | present e =>
        simp [encodeLiteral, decodeLiteralRaw, tagged, Tag.parse_text,
          AuditWire.decode_encodeStamped n unique e valid]
    | absent e =>
        simp [encodeLiteral, decodeLiteralRaw, tagged, Tag.parse_text,
          AuditWire.decode_encodeStamped n unique e valid]
    | before a b =>
        obtain ⟨ha, hb⟩ := valid
        simp [encodeLiteral, decodeLiteralRaw, tagged, Tag.parse_text,
          AuditWire.decode_encodeStamped n unique a ha, AuditWire.decode_encodeStamped n unique b hb]
    | formula q =>
        simp [encodeLiteral, decodeLiteralRaw, tagged, Tag.parse_text,
          InquiryProcessWire.decode_encodeQuery n unique q valid]
    | notFormula q =>
        simp [encodeLiteral, decodeLiteralRaw, tagged, Tag.parse_text,
          InquiryProcessWire.decode_encodeQuery n unique q valid]
  unfold decodeLiteral Source.Wire.canonical
  rw [hraw]
  simp

theorem encodeLiteral_injective (n : Names) (unique : UniqueNames n)
    {a b : Literal} (ha : LiteralWellNamed n a) (hb : LiteralWellNamed n b)
    (h : encodeLiteral n a = encodeLiteral n b) : a = b :=
  injective_on_of_roundtrip _ _ _ (decode_encodeLiteral n unique) ha hb h

/-! ### Sensitivity rows -/

def SensitivityRowWellNamed (n : Names) (row : SensitivityRow) : Prop :=
  CompletionWellNamed n row.completion

def encodeSensitivityRow (n : Names) (row : SensitivityRow) : Sx :=
  tagged .row [encodeCompletion n row.completion, encodeList encodeSlotId row.changed]

def decodeSensitivityRow (n : Names) : Sx → Option SensitivityRow
  | .list (.atom t :: [c, ch]) =>
      if t = (Tag.row).text then
        (match decodeCompletion n c, decodeList decodeSlotId ch with
         | some completion, some changed => some ⟨completion, changed⟩ | _, _ => none)
      else none
  | _ => none

theorem decode_encodeSensitivityRow (n : Names) (unique : UniqueNames n) (row : SensitivityRow)
    (valid : SensitivityRowWellNamed n row) :
    decodeSensitivityRow n (encodeSensitivityRow n row) = some row := by
  obtain ⟨completion, changed⟩ := row
  simp [encodeSensitivityRow, decodeSensitivityRow, tagged,
    Family.Wire.decode_encodeCompletion n unique completion valid, decode_encodeList]

theorem encodeSensitivityRow_injective (n : Names) (unique : UniqueNames n)
    {a b : SensitivityRow} (ha : SensitivityRowWellNamed n a) (hb : SensitivityRowWellNamed n b)
    (h : encodeSensitivityRow n a = encodeSensitivityRow n b) : a = b :=
  injective_on_of_roundtrip _ _ _ (decode_encodeSensitivityRow n unique) ha hb h

/-! ### Stability result -/

def StabilityResultWellNamed (n : Names) (r : StabilityResult ObservableSpec) : Prop :=
  ObservableWellNamed n r.observable

def encodeStabilityResult (n : Names) (r : StabilityResult ObservableSpec) : Sx :=
  tagged .stabilityResult [encodeObservableSpec n r.observable, Process.Wire.encodeNat r.total,
    Process.Wire.encodeNat r.accepted, Process.Wire.encodeNat r.rejected,
    encodeBool r.wholeStable, encodeBool r.acceptedDomainStable]

def decodeStabilityResultRaw (n : Names) : Sx → Option (StabilityResult ObservableSpec)
  | .list (.atom t :: [obs, total, accepted, rejected, ws, ads]) =>
      if t = (Tag.stabilityResult).text then do
        let obs' ← decodeObservableSpec n obs
        let total' ← (Process.Wire.decodeNat total).toOption
        let accepted' ← (Process.Wire.decodeNat accepted).toOption
        let rejected' ← (Process.Wire.decodeNat rejected).toOption
        let ws' ← decodeBool ws
        let ads' ← decodeBool ads
        return ⟨obs', total', accepted', rejected', ws', ads'⟩
      else none
  | _ => none

def decodeStabilityResult (n : Names) (wire : Sx) : Option (StabilityResult ObservableSpec) :=
  Source.Wire.canonical (encodeStabilityResult n) (decodeStabilityResultRaw n) wire

theorem decodeStabilityResult_canonical (n : Names) {wire : Sx} {value : StabilityResult ObservableSpec}
    (h : decodeStabilityResult n wire = some value) : encodeStabilityResult n value = wire :=
  Source.Wire.canonical_sound _ _ h

theorem decode_encodeStabilityResult (n : Names) (unique : UniqueNames n)
    (value : StabilityResult ObservableSpec) (valid : StabilityResultWellNamed n value) :
    decodeStabilityResult n (encodeStabilityResult n value) = some value := by
  obtain ⟨obs, total, accepted, rejected, ws, ads⟩ := value
  have hraw : decodeStabilityResultRaw n (encodeStabilityResult n
      ⟨obs, total, accepted, rejected, ws, ads⟩) =
      some ⟨obs, total, accepted, rejected, ws, ads⟩ := by
    simp [encodeStabilityResult, decodeStabilityResultRaw, tagged,
      decode_encodeObservableSpec n unique obs valid, InquiryProcessWire.decode_encodeNat,
      AuditWire.decode_encodeBool]
  unfold decodeStabilityResult Source.Wire.canonical
  rw [hraw]
  simp

theorem encodeStabilityResult_injective (n : Names) (unique : UniqueNames n)
    {a b : StabilityResult ObservableSpec} (ha : StabilityResultWellNamed n a)
    (hb : StabilityResultWellNamed n b)
    (h : encodeStabilityResult n a = encodeStabilityResult n b) : a = b :=
  injective_on_of_roundtrip _ _ _ (decode_encodeStabilityResult n unique) ha hb h

/-! ### Sensitivity result -/

def SensitivityResultWellNamed (n : Names) (r : SensitivityResult ObservableSpec) : Prop :=
  ObservableWellNamed n r.observable ∧ CompletionWellNamed n r.reference ∧
    (∀ row ∈ r.differing, SensitivityRowWellNamed n row) ∧
    ∀ p ∈ r.realizing, CompletionWellNamed n p.2

def encodeSensitivityResult (n : Names) (r : SensitivityResult ObservableSpec) : Sx :=
  tagged .sensitivityResult [encodeObservableSpec n r.observable, encodeCompletion n r.reference,
    Process.Wire.encodeNat r.total, Process.Wire.encodeNat r.sensitive,
    encodeList (encodeSensitivityRow n) r.differing,
    encodeList (encodeList encodeSlotId) r.minimalSlotSets,
    encodeList (encodePair (encodeList encodeSlotId) (encodeCompletion n)) r.realizing]

def decodeSensitivityResultRaw (n : Names) : Sx → Option (SensitivityResult ObservableSpec)
  | .list (.atom t :: [obs, ref, total, sensitive, diff, minimal, real]) =>
      if t = (Tag.sensitivityResult).text then do
        let obs' ← decodeObservableSpec n obs
        let ref' ← decodeCompletion n ref
        let total' ← (Process.Wire.decodeNat total).toOption
        let sensitive' ← (Process.Wire.decodeNat sensitive).toOption
        let diff' ← decodeList (decodeSensitivityRow n) diff
        let minimal' ← decodeList (decodeList decodeSlotId) minimal
        let real' ← decodeList (decodePair (decodeList decodeSlotId) (decodeCompletion n)) real
        return ⟨obs', ref', total', sensitive', diff', minimal', real'⟩
      else none
  | _ => none

def decodeSensitivityResult (n : Names) (wire : Sx) : Option (SensitivityResult ObservableSpec) :=
  Source.Wire.canonical (encodeSensitivityResult n) (decodeSensitivityResultRaw n) wire

theorem decodeSensitivityResult_canonical (n : Names) {wire : Sx}
    {value : SensitivityResult ObservableSpec}
    (h : decodeSensitivityResult n wire = some value) : encodeSensitivityResult n value = wire :=
  Source.Wire.canonical_sound _ _ h

theorem decode_encodeSensitivityResult (n : Names) (unique : UniqueNames n)
    (value : SensitivityResult ObservableSpec) (valid : SensitivityResultWellNamed n value) :
    decodeSensitivityResult n (encodeSensitivityResult n value) = some value := by
  obtain ⟨obs, ref, total, sensitive, diff, minimal, real⟩ := value
  obtain ⟨hobs, href, hdiff, hreal⟩ := valid
  have hpair : ∀ p ∈ real, CompletionWellNamed n p.2 := fun p hp => hreal p hp
  have hpairrt : ∀ p, CompletionWellNamed n p.2 →
      decodePair (decodeList decodeSlotId) (decodeCompletion n)
        (encodePair (encodeList encodeSlotId) (encodeCompletion n) p) = some p :=
    fun p hp => decode_encodePair_of (encodeList encodeSlotId) (encodeCompletion n)
      (decodeList decodeSlotId) (decodeCompletion n) (fun _ => True) (CompletionWellNamed n)
      (fun xs _ => decode_encodeList encodeSlotId decodeSlotId Family.Wire.decode_encodeSlotId xs)
      (Family.Wire.decode_encodeCompletion n unique) p ⟨trivial, hp⟩
  have hraw : decodeSensitivityResultRaw n (encodeSensitivityResult n
      ⟨obs, ref, total, sensitive, diff, minimal, real⟩) =
      some ⟨obs, ref, total, sensitive, diff, minimal, real⟩ := by
    simp [encodeSensitivityResult, decodeSensitivityResultRaw, tagged,
      decode_encodeObservableSpec n unique obs hobs,
      Family.Wire.decode_encodeCompletion n unique ref href, InquiryProcessWire.decode_encodeNat,
      decode_encodeList_of _ _ _ (decode_encodeSensitivityRow n unique) diff hdiff,
      decode_encodeList, decode_encodeList_of _ _ _ hpairrt real hpair]
  unfold decodeSensitivityResult Source.Wire.canonical
  rw [hraw]
  simp

theorem encodeSensitivityResult_injective (n : Names) (unique : UniqueNames n)
    {a b : SensitivityResult ObservableSpec} (ha : SensitivityResultWellNamed n a)
    (hb : SensitivityResultWellNamed n b)
    (h : encodeSensitivityResult n a = encodeSensitivityResult n b) : a = b :=
  injective_on_of_roundtrip _ _ _ (decode_encodeSensitivityResult n unique) ha hb h

/-! ### Deletion, minimal set and minimal-assumptions result -/

def DeletionWellNamed (n : Names) (d : Deletion) : Prop :=
  LiteralWellNamed n d.literal ∧ (∀ c ∈ d.surviving, CompletionWellNamed n c) ∧
    ∀ c ∈ d.counter, CompletionWellNamed n c

def encodeDeletion (n : Names) (d : Deletion) : Sx :=
  tagged .deletion [encodeLiteral n d.literal, encodeList (encodeCompletion n) d.surviving,
    encodeOpt (encodeCompletion n) d.counter]

def decodeDeletion (n : Names) : Sx → Option Deletion
  | .list (.atom t :: [lit, surviving, counter]) =>
      if t = (Tag.deletion).text then do
        return ⟨← decodeLiteral n lit, ← decodeList (decodeCompletion n) surviving,
          ← decodeOpt (decodeCompletion n) counter⟩
      else none
  | _ => none

theorem decode_encodeDeletion (n : Names) (unique : UniqueNames n) (value : Deletion)
    (valid : DeletionWellNamed n value) :
    decodeDeletion n (encodeDeletion n value) = some value := by
  obtain ⟨lit, surviving, counter⟩ := value
  obtain ⟨hlit, hsurv, hcount⟩ := valid
  simp [encodeDeletion, decodeDeletion, tagged,
    decode_encodeLiteral n unique lit hlit,
    decode_encodeList_of _ _ _ (Family.Wire.decode_encodeCompletion n unique) surviving hsurv,
    decode_encodeOpt_of _ _ _ (Family.Wire.decode_encodeCompletion n unique) counter hcount]

def MinimalSetWellNamed (n : Names) (s : MinimalSet) : Prop :=
  (∀ lit ∈ s.literals, LiteralWellNamed n lit) ∧
    (∀ c ∈ s.surviving, CompletionWellNamed n c) ∧
    ∀ d ∈ s.deletions, DeletionWellNamed n d

def encodeMinimalSet (n : Names) (s : MinimalSet) : Sx :=
  tagged .minimalSet [encodeList (encodeLiteral n) s.literals,
    encodeList (encodeCompletion n) s.surviving, encodeList (encodeDeletion n) s.deletions]

def decodeMinimalSet (n : Names) : Sx → Option MinimalSet
  | .list (.atom t :: [lits, surviving, deletions]) =>
      if t = (Tag.minimalSet).text then do
        return ⟨← decodeList (decodeLiteral n) lits, ← decodeList (decodeCompletion n) surviving,
          ← decodeList (decodeDeletion n) deletions⟩
      else none
  | _ => none

theorem decode_encodeMinimalSet (n : Names) (unique : UniqueNames n) (value : MinimalSet)
    (valid : MinimalSetWellNamed n value) :
    decodeMinimalSet n (encodeMinimalSet n value) = some value := by
  obtain ⟨lits, surviving, deletions⟩ := value
  obtain ⟨hlits, hsurv, hdel⟩ := valid
  simp [encodeMinimalSet, decodeMinimalSet, tagged,
    decode_encodeList_of _ _ _ (decode_encodeLiteral n unique) lits hlits,
    decode_encodeList_of _ _ _ (Family.Wire.decode_encodeCompletion n unique) surviving hsurv,
    decode_encodeList_of _ _ _ (decode_encodeDeletion n unique) deletions hdel]

def AssumptionResultWellNamed (n : Names) (r : AssumptionResult TargetSpec) : Prop :=
  TargetWellNamed n r.target ∧ (∀ lit ∈ r.catalog, LiteralWellNamed n lit) ∧
    ∀ s ∈ r.minimal, MinimalSetWellNamed n s

def encodeAssumptionResult (n : Names) (r : AssumptionResult TargetSpec) : Sx :=
  tagged .assumptionResult [encodeTargetSpec n r.target, encodeList (encodeLiteral n) r.catalog,
    Process.Wire.encodeNat r.total, encodeList (encodeMinimalSet n) r.minimal]

def decodeAssumptionResultRaw (n : Names) : Sx → Option (AssumptionResult TargetSpec)
  | .list (.atom t :: [tgt, catalog, total, minimal]) =>
      if t = (Tag.assumptionResult).text then do
        let tgt' ← decodeTargetSpec n tgt
        let catalog' ← decodeList (decodeLiteral n) catalog
        let total' ← (Process.Wire.decodeNat total).toOption
        let minimal' ← decodeList (decodeMinimalSet n) minimal
        return { target := tgt', catalog := catalog', total := total', minimal := minimal' }
      else none
  | _ => none

def decodeAssumptionResult (n : Names) (wire : Sx) : Option (AssumptionResult TargetSpec) :=
  Source.Wire.canonical (encodeAssumptionResult n) (decodeAssumptionResultRaw n) wire

theorem decodeAssumptionResult_canonical (n : Names) {wire : Sx}
    {value : AssumptionResult TargetSpec}
    (h : decodeAssumptionResult n wire = some value) : encodeAssumptionResult n value = wire :=
  Source.Wire.canonical_sound _ _ h

theorem decode_encodeAssumptionResult (n : Names) (unique : UniqueNames n)
    (value : AssumptionResult TargetSpec) (valid : AssumptionResultWellNamed n value) :
    decodeAssumptionResult n (encodeAssumptionResult n value) = some value := by
  obtain ⟨tgt, catalog, total, minimal⟩ := value
  obtain ⟨htgt, hcat, hmin⟩ := valid
  have hraw : decodeAssumptionResultRaw n (encodeAssumptionResult n
      ⟨tgt, catalog, total, minimal⟩) = some ⟨tgt, catalog, total, minimal⟩ := by
    simp [encodeAssumptionResult, decodeAssumptionResultRaw, tagged,
      decode_encodeTargetSpec n unique tgt htgt,
      decode_encodeList_of _ _ _ (decode_encodeLiteral n unique) catalog hcat,
      decode_encodeList_of _ _ _ (decode_encodeMinimalSet n unique) minimal hmin,
      InquiryProcessWire.decode_encodeNat]
  unfold decodeAssumptionResult Source.Wire.canonical
  rw [hraw]
  simp

theorem encodeAssumptionResult_injective (n : Names) (unique : UniqueNames n)
    {a b : AssumptionResult TargetSpec} (ha : AssumptionResultWellNamed n a)
    (hb : AssumptionResultWellNamed n b)
    (h : encodeAssumptionResult n a = encodeAssumptionResult n b) : a = b :=
  injective_on_of_roundtrip _ _ _ (decode_encodeAssumptionResult n unique) ha hb h

end Lara.Process.Analysis.AnalysisWire
