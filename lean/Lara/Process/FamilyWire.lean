import Lara.Process.Family
import Lara.Process.SourceWire
import Lara.Process.InquiryProcessWire

/-!
Typed, finite family components at the Driver S-expression boundary. Process
queries and events retain the P0 names context; source fragments retain authored
declaration order and sugar. Slot and choice identities are canonical naturals,
not fragment hashes. This module does not encode FamilySpec or run an observer.
-/
namespace Lara.Process.Family.Wire

open Lara.Driver (Sx)
open Lara.Process.InquiryProcessWire

inductive Tag where
  | truth | query | present | before | not | and | or
  | choiceId | slotId | choice | slot | selection | completion
  deriving DecidableEq, Repr

def Tag.text : Tag → String
  | .truth => "truth" | .query => "query" | .present => "present"
  | .before => "before" | .not => "not" | .and => "and" | .or => "or"
  | .choiceId => "choice-id" | .slotId => "slot-id"
  | .choice => "choice" | .slot => "slot" | .selection => "selection"
  | .completion => "completion"

def Tag.spelling : Process.Wire.Spelling Tag where
  all := [.truth, .query, .present, .before, .not, .and, .or,
    .choiceId, .slotId, .choice, .slot, .selection, .completion]
  text := Tag.text

def Tag.parse : String → Option Tag := Tag.spelling.parse

theorem Tag.spelling_complete (tag : Tag) : tag ∈ Tag.spelling.all := by cases tag <;> decide

theorem Tag.spelling_nodup : (Tag.spelling.all.map Tag.spelling.text).Nodup := by decide

@[simp] theorem Tag.parse_text (tag : Tag) : Tag.parse tag.text = some tag :=
  Tag.spelling.parse_text Tag.spelling_complete Tag.spelling_nodup tag

theorem Tag.parse_some {text : String} {tag : Tag} (h : Tag.parse text = some tag) :
    tag.text = text := Tag.spelling.parse_some h

theorem Tag.text_injective : Function.Injective Tag.text :=
  Tag.spelling.text_injective Tag.spelling_complete Tag.spelling_nodup

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

private theorem decodeList_canonical (encode : α → Sx) (decode : Sx → Option α)
    (canonical : ∀ {wire a}, decode wire = some a → encode a = wire)
    {wires : List Sx} {values : List α}
    (h : Source.Wire.decodeList decode wires = some values) : values.map encode = wires := by
  induction wires generalizing values with
  | nil => simp only [Source.Wire.decodeList, Option.some.injEq] at h; subst h; rfl
  | cons wire wires ih =>
      simp only [Source.Wire.decodeList, bind_some_iff, pure_some_iff] at h
      obtain ⟨a, ha, rest, hr, rfl⟩ := h
      simp [canonical ha, ih hr]

private theorem decodeList_map_of (encode : α → Sx) (decode : Sx → Option α)
    (p : α → Prop) (roundtrip : ∀ a, p a → decode (encode a) = some a)
    (values : List α) (valid : ∀ a ∈ values, p a) :
    Source.Wire.decodeList decode (values.map encode) = some values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at valid
      simp [Source.Wire.decodeList, roundtrip value valid.1, ih valid.2]

private theorem injective_on_of_roundtrip (encode : α → Sx) (decode : Sx → Option α)
    (p : α → Prop) (roundtrip : ∀ a, p a → decode (encode a) = some a)
    {a b : α} (ha : p a) (hb : p b) (equal : encode a = encode b) : a = b := by
  have h := congrArg decode equal
  simpa only [roundtrip a ha, roundtrip b hb, Option.some.injEq] using h

def encodeSlotId (id : SlotId) : Sx :=
  .list [.atom Tag.slotId.text, Process.Wire.encodeNat id.index]

def decodeSlotId : Sx → Option SlotId
  | .list [.atom raw, index] =>
      match Tag.parse raw with
      | some .slotId => (Process.Wire.decodeNat index).toOption.map SlotId.mk
      | _ => none
  | _ => none

def encodeChoiceId (id : ChoiceId) : Sx :=
  .list [.atom Tag.choiceId.text, Process.Wire.encodeNat id.index]

def decodeChoiceId : Sx → Option ChoiceId
  | .list [.atom raw, index] =>
      match Tag.parse raw with
      | some .choiceId => (Process.Wire.decodeNat index).toOption.map ChoiceId.mk
      | _ => none
  | _ => none

@[simp] theorem decode_encodeSlotId (id : SlotId) : decodeSlotId (encodeSlotId id) = some id := by
  cases id; simp [decodeSlotId, encodeSlotId, Except.toOption]

@[simp] theorem decode_encodeChoiceId (id : ChoiceId) :
    decodeChoiceId (encodeChoiceId id) = some id := by
  cases id; simp [decodeChoiceId, encodeChoiceId, Except.toOption]

theorem decodeSlotId_canonical {wire : Sx} {id : SlotId}
    (h : decodeSlotId wire = some id) : encodeSlotId id = wire := by
  unfold decodeSlotId at h
  split at h
  · split at h
    · rename_i raw index parsed
      simp only [Option.map_eq_some_iff, except_toOption_some] at h
      obtain ⟨value, hv, rfl⟩ := h
      simp [encodeSlotId, Tag.parse_some parsed, Process.Wire.decodeNat_canonical hv]
    · cases h
  · cases h

theorem decodeChoiceId_canonical {wire : Sx} {id : ChoiceId}
    (h : decodeChoiceId wire = some id) : encodeChoiceId id = wire := by
  unfold decodeChoiceId at h
  split at h
  · split at h
    · rename_i raw index parsed
      simp only [Option.map_eq_some_iff, except_toOption_some] at h
      obtain ⟨value, hv, rfl⟩ := h
      simp [encodeChoiceId, Tag.parse_some parsed, Process.Wire.decodeNat_canonical hv]
    · cases h
  · cases h

theorem encodeSlotId_injective : Function.Injective encodeSlotId :=
  Source.Wire.injective_of_roundtrip _ _ decode_encodeSlotId

theorem encodeChoiceId_injective : Function.Injective encodeChoiceId :=
  Source.Wire.injective_of_roundtrip _ _ decode_encodeChoiceId

/-- Only contextual process identifiers need bounds; all guard constructors remain available. -/
def GuardWellNamed (names : Process.Wire.Names) : Guard → Prop
  | .truth => True
  | .query query => QueryWellNamed names query
  | .present event => StampedWellNamed names event
  | .before first second => StampedWellNamed names first ∧ StampedWellNamed names second
  | .not guard => GuardWellNamed names guard
  | .and left right | .or left right => GuardWellNamed names left ∧ GuardWellNamed names right

def ChoiceWellNamed (names : Process.Wire.Names) (choice : Choice) : Prop :=
  GuardWellNamed names choice.guard

def SlotWellNamed (names : Process.Wire.Names) (slot : Slot) : Prop :=
  ∀ choice ∈ slot.choices, ChoiceWellNamed names choice

def SelectionWellNamed (names : Process.Wire.Names) (selection : Selection) : Prop :=
  ChoiceWellNamed names selection.choice

def CompletionWellNamed (names : Process.Wire.Names) (completion : Completion) : Prop :=
  (∀ event ∈ completion.history, StampedWellNamed names event) ∧
    ∀ selection ∈ completion.assignment, SelectionWellNamed names selection

def encodeGuard (names : Process.Wire.Names) : Guard → Sx
  | .truth => .list [.atom Tag.truth.text]
  | .query query => .list [.atom Tag.query.text, Process.Wire.encodeQuery names query]
  | .present event => .list [.atom Tag.present.text, Process.Wire.encodeStamped names event]
  | .before first second => .list [.atom Tag.before.text,
      Process.Wire.encodeStamped names first, Process.Wire.encodeStamped names second]
  | .not guard => .list [.atom Tag.not.text, encodeGuard names guard]
  | .and left right => .list [.atom Tag.and.text, encodeGuard names left, encodeGuard names right]
  | .or left right => .list [.atom Tag.or.text, encodeGuard names left, encodeGuard names right]

def decodeGuard (names : Process.Wire.Names) : Sx → Option Guard
  | .list [.atom raw] =>
      match Tag.parse raw with
      | some .truth => some .truth
      | _ => none
  | .list [.atom raw, arg] =>
      match Tag.parse raw with
      | some .query => (Process.Wire.decodeQuery names arg).toOption.map Guard.query
      | some .present => (Process.Wire.decodeStamped names arg).toOption.map Guard.present
      | some .not => (decodeGuard names arg).map Guard.not
      | _ => none
  | .list [.atom raw, left, right] =>
      match Tag.parse raw with
      | some .before => do
          return .before (← (Process.Wire.decodeStamped names left).toOption)
            (← (Process.Wire.decodeStamped names right).toOption)
      | some .and => do return .and (← decodeGuard names left) (← decodeGuard names right)
      | some .or => do return .or (← decodeGuard names left) (← decodeGuard names right)
      | _ => none
  | _ => none

theorem decode_encodeGuard (names : Process.Wire.Names) (unique : UniqueNames names)
    (guard : Guard) (valid : GuardWellNamed names guard) :
    decodeGuard names (encodeGuard names guard) = some guard := by
  induction guard with
  | truth => simp [encodeGuard, decodeGuard]
  | query query => simp [encodeGuard, decodeGuard, decode_encodeQuery names unique query valid,
      Except.toOption]
  | present event => simp [encodeGuard, decodeGuard, decode_encodeStamped names unique event valid,
      Except.toOption]
  | before first second => simp [encodeGuard, decodeGuard,
      decode_encodeStamped names unique first valid.1,
      decode_encodeStamped names unique second valid.2, Except.toOption]
  | not guard ih => simp [encodeGuard, decodeGuard, ih valid]
  | and left right il ir => simp [encodeGuard, decodeGuard, il valid.1, ir valid.2]
  | or left right il ir => simp [encodeGuard, decodeGuard, il valid.1, ir valid.2]

theorem decodeGuard_canonical (names : Process.Wire.Names) :
    ∀ {wire : Sx} {guard : Guard}, decodeGuard names wire = some guard → encodeGuard names guard = wire
  | .list [.atom raw], guard, h => by
      unfold decodeGuard at h
      split at h
      · rename_i parsed; cases h; simp [encodeGuard, Tag.parse_some parsed]
      · cases h
  | .list [.atom raw, arg], guard, h => by
      unfold decodeGuard at h
      split at h
      · rename_i parsed
        simp only [Option.map_eq_some_iff, except_toOption_some] at h
        obtain ⟨query, hq, rfl⟩ := h
        simp [encodeGuard, Tag.parse_some parsed, Process.Wire.decodeQuery_canonical names hq]
      · rename_i parsed
        simp only [Option.map_eq_some_iff, except_toOption_some] at h
        obtain ⟨event, he, rfl⟩ := h
        simp [encodeGuard, Tag.parse_some parsed, Process.Wire.decodeStamped_canonical names he]
      · rename_i parsed
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨guard, hg, rfl⟩ := h
        simp [encodeGuard, Tag.parse_some parsed, decodeGuard_canonical names hg]
      · cases h
  | .list [.atom raw, left, right], guard, h => by
      unfold decodeGuard at h
      split at h
      · rename_i parsed
        simp only [bind_some_iff, pure_some_iff, except_toOption_some] at h
        obtain ⟨first, hf, second, hs, rfl⟩ := h
        simp [encodeGuard, Tag.parse_some parsed, Process.Wire.decodeStamped_canonical names hf,
          Process.Wire.decodeStamped_canonical names hs]
      · rename_i parsed
        simp only [bind_some_iff, pure_some_iff] at h
        obtain ⟨first, hf, second, hs, rfl⟩ := h
        simp [encodeGuard, Tag.parse_some parsed, decodeGuard_canonical names hf,
          decodeGuard_canonical names hs]
      · rename_i parsed
        simp only [bind_some_iff, pure_some_iff] at h
        obtain ⟨first, hf, second, hs, rfl⟩ := h
        simp [encodeGuard, Tag.parse_some parsed, decodeGuard_canonical names hf,
          decodeGuard_canonical names hs]
      · cases h
  | .atom _, _, h => by simp [decodeGuard] at h
  | .list [], _, h => by simp [decodeGuard] at h
  | .list (.list _ :: _), _, h => by simp [decodeGuard] at h
  | .list (.atom _ :: _ :: _ :: _ :: _), _, h => by simp [decodeGuard] at h

def encodeChoice (names : Process.Wire.Names) (choice : Choice) : Sx :=
  .list [.atom Tag.choice.text, encodeChoiceId choice.id, encodeGuard names choice.guard,
    Source.Wire.encodeFragment choice.fragment]

def decodeChoice (names : Process.Wire.Names) : Sx → Option Choice
  | .list [.atom raw, id, guard, fragment] =>
      match Tag.parse raw with
      | some .choice => do return ⟨← decodeChoiceId id, ← decodeGuard names guard,
          ← Source.Wire.decodeFragment fragment⟩
      | _ => none
  | _ => none

def encodeSlot (names : Process.Wire.Names) (slot : Slot) : Sx :=
  .list [.atom Tag.slot.text, encodeSlotId slot.id, .list (slot.choices.map (encodeChoice names))]

def decodeSlot (names : Process.Wire.Names) : Sx → Option Slot
  | .list [.atom raw, id, .list choices] =>
      match Tag.parse raw with
      | some .slot => do return ⟨← decodeSlotId id, ← Source.Wire.decodeList (decodeChoice names) choices⟩
      | _ => none
  | _ => none

def encodeSelection (names : Process.Wire.Names) (selection : Selection) : Sx :=
  .list [.atom Tag.selection.text, encodeSlotId selection.slot, encodeChoice names selection.choice]

def decodeSelection (names : Process.Wire.Names) : Sx → Option Selection
  | .list [.atom raw, slot, choice] =>
      match Tag.parse raw with
      | some .selection => do return ⟨← decodeSlotId slot, ← decodeChoice names choice⟩
      | _ => none
  | _ => none

def encodeCompletion (names : Process.Wire.Names) (completion : Completion) : Sx :=
  .list [.atom Tag.completion.text,
    .list (completion.history.map (Process.Wire.encodeStamped names)),
    .list (completion.assignment.map (encodeSelection names))]

def decodeCompletion (names : Process.Wire.Names) : Sx → Option Completion
  | .list [.atom raw, .list history, .list assignment] =>
      match Tag.parse raw with
      | some .completion => do
          return ⟨← Source.Wire.decodeList
            (fun wire => (Process.Wire.decodeStamped names wire).toOption) history,
            ← Source.Wire.decodeList (decodeSelection names) assignment⟩
      | _ => none
  | _ => none

theorem decode_encodeChoice (names : Process.Wire.Names) (unique : UniqueNames names)
    (choice : Choice) (valid : ChoiceWellNamed names choice) :
    decodeChoice names (encodeChoice names choice) = some choice := by
  cases choice; simp [encodeChoice, decodeChoice, decode_encodeGuard names unique _ valid]

theorem decode_encodeSlot (names : Process.Wire.Names) (unique : UniqueNames names)
    (slot : Slot) (valid : SlotWellNamed names slot) :
    decodeSlot names (encodeSlot names slot) = some slot := by
  cases slot
  simp [encodeSlot, decodeSlot, decodeList_map_of _ _ _ (decode_encodeChoice names unique) _ valid]

theorem decode_encodeSelection (names : Process.Wire.Names) (unique : UniqueNames names)
    (selection : Selection) (valid : SelectionWellNamed names selection) :
    decodeSelection names (encodeSelection names selection) = some selection := by
  cases selection; simp [encodeSelection, decodeSelection, decode_encodeChoice names unique _ valid]

theorem decode_encodeCompletion (names : Process.Wire.Names) (unique : UniqueNames names)
    (completion : Completion) (valid : CompletionWellNamed names completion) :
    decodeCompletion names (encodeCompletion names completion) = some completion := by
  have events : ∀ event, StampedWellNamed names event →
      (Process.Wire.decodeStamped names (Process.Wire.encodeStamped names event)).toOption = some event :=
    fun event valid => except_toOption_some.mpr (decode_encodeStamped names unique event valid)
  cases completion
  simp [encodeCompletion, decodeCompletion,
    decodeList_map_of (Process.Wire.encodeStamped names)
      (fun wire => (Process.Wire.decodeStamped names wire).toOption) _ events _ valid.1,
    decodeList_map_of _ _ _ (decode_encodeSelection names unique) _ valid.2]

theorem decodeChoice_canonical (names : Process.Wire.Names) {wire : Sx} {choice : Choice}
    (h : decodeChoice names wire = some choice) : encodeChoice names choice = wire := by
  unfold decodeChoice at h
  split at h
  · split at h
    · rename_i raw id guard fragment parsed
      simp only [bind_some_iff, pure_some_iff] at h
      obtain ⟨id, hi, guard, hg, fragment, hf, rfl⟩ := h
      simp [encodeChoice, Tag.parse_some parsed, decodeChoiceId_canonical hi,
        decodeGuard_canonical names hg, Source.Wire.decodeFragment_canonical hf]
    · cases h
  · cases h

theorem decodeSlot_canonical (names : Process.Wire.Names) {wire : Sx} {slot : Slot}
    (h : decodeSlot names wire = some slot) : encodeSlot names slot = wire := by
  unfold decodeSlot at h
  split at h
  · split at h
    · rename_i raw id choices parsed
      simp only [bind_some_iff, pure_some_iff] at h
      obtain ⟨id, hi, choices, hc, rfl⟩ := h
      simp [encodeSlot, Tag.parse_some parsed, decodeSlotId_canonical hi,
        decodeList_canonical _ _ (decodeChoice_canonical names) hc]
    · cases h
  · cases h

theorem decodeSelection_canonical (names : Process.Wire.Names) {wire : Sx} {selection : Selection}
    (h : decodeSelection names wire = some selection) : encodeSelection names selection = wire := by
  unfold decodeSelection at h
  split at h
  · split at h
    · rename_i raw slot choice parsed
      simp only [bind_some_iff, pure_some_iff] at h
      obtain ⟨slot, hs, choice, hc, rfl⟩ := h
      simp [encodeSelection, Tag.parse_some parsed, decodeSlotId_canonical hs,
        decodeChoice_canonical names hc]
    · cases h
  · cases h

theorem decodeCompletion_canonical (names : Process.Wire.Names) {wire : Sx} {completion : Completion}
    (h : decodeCompletion names wire = some completion) : encodeCompletion names completion = wire := by
  have events : ∀ {wire event}, (Process.Wire.decodeStamped names wire).toOption = some event →
      Process.Wire.encodeStamped names event = wire :=
    fun h => Process.Wire.decodeStamped_canonical names (except_toOption_some.mp h)
  unfold decodeCompletion at h
  split at h
  · split at h
    · rename_i raw history assignment parsed
      simp only [bind_some_iff, pure_some_iff] at h
      obtain ⟨history, hh, assignment, ha, rfl⟩ := h
      simp [encodeCompletion, Tag.parse_some parsed,
        decodeList_canonical (Process.Wire.encodeStamped names)
          (fun wire => (Process.Wire.decodeStamped names wire).toOption) events hh,
        decodeList_canonical _ _ (decodeSelection_canonical names) ha]
    · cases h
  · cases h

theorem encodeGuard_injective (names : Process.Wire.Names) (unique : UniqueNames names)
    {a b : Guard} (ha : GuardWellNamed names a) (hb : GuardWellNamed names b)
    (h : encodeGuard names a = encodeGuard names b) : a = b :=
  injective_on_of_roundtrip _ _ _ (decode_encodeGuard names unique) ha hb h

theorem encodeChoice_injective (names : Process.Wire.Names) (unique : UniqueNames names)
    {a b : Choice} (ha : ChoiceWellNamed names a) (hb : ChoiceWellNamed names b)
    (h : encodeChoice names a = encodeChoice names b) : a = b :=
  injective_on_of_roundtrip _ _ _ (decode_encodeChoice names unique) ha hb h

theorem encodeSlot_injective (names : Process.Wire.Names) (unique : UniqueNames names)
    {a b : Slot} (ha : SlotWellNamed names a) (hb : SlotWellNamed names b)
    (h : encodeSlot names a = encodeSlot names b) : a = b :=
  injective_on_of_roundtrip _ _ _ (decode_encodeSlot names unique) ha hb h

theorem encodeSelection_injective (names : Process.Wire.Names) (unique : UniqueNames names)
    {a b : Selection} (ha : SelectionWellNamed names a) (hb : SelectionWellNamed names b)
    (h : encodeSelection names a = encodeSelection names b) : a = b :=
  injective_on_of_roundtrip _ _ _ (decode_encodeSelection names unique) ha hb h

theorem encodeCompletion_injective (names : Process.Wire.Names) (unique : UniqueNames names)
    {a b : Completion} (ha : CompletionWellNamed names a) (hb : CompletionWellNamed names b)
    (h : encodeCompletion names a = encodeCompletion names b) : a = b :=
  injective_on_of_roundtrip _ _ _ (decode_encodeCompletion names unique) ha hb h

end Lara.Process.Family.Wire
