import Lara.Process.Wire

/-!
Name-bound roundtrips for the existing P0 event and query codecs. Unique tables
and structural index bounds are independent of decoding; neither P0 syntax nor
its out-of-range encoder behavior is changed here.
-/
namespace Lara.Process.InquiryProcessWire

open Lara.Process.Wire
open Lara.Driver (Sx)

/-- Each namespace interns names without aliases. -/
def UniqueNames (n : Names) : Prop :=
  n.event.Nodup ∧ n.actor.Nodup ∧ n.plan.Nodup ∧ n.run.Nodup ∧
    n.claim.Nodup ∧ n.source.Nodup ∧ n.data.Nodup ∧ n.family.Nodup ∧ n.witness.Nodup

def InputWellNamed (n : Names) (input : DataId × VersionId) : Prop :=
  input.1.index < n.data.length

def EventWellNamed (n : Names) : Event → Prop
  | .commitPlan actor plan _ => actor.index < n.actor.length ∧ plan.index < n.plan.length
  | .access actor data _ => actor.index < n.actor.length ∧ data.index < n.data.length
  | .run run plan _ inputs family => run.index < n.run.length ∧ plan.index < n.plan.length ∧
      (∀ input ∈ inputs, InputWellNamed n input) ∧ family.index < n.family.length
  | .result run _ => run.index < n.run.length
  | .assert claim witness => claim.index < n.claim.length ∧ witness.index < n.witness.length
  | .retract source => source.index < n.source.length
  | .updateData data _ => data.index < n.data.length

def StampedWellNamed (n : Names) (event : Stamped) : Prop :=
  event.id.index < n.event.length ∧ EventWellNamed n event.event

def AtomWellNamed (n : Names) : Universe.Atom → Prop
  | .predictable => True
  | .runPrecommitted run => run.index < n.run.length
  | .splitSelection selection test =>
      (∀ data ∈ selection, data.index < n.data.length) ∧
      (∀ data ∈ test, data.index < n.data.length)
  | .familyCountAtMost family _ => family.index < n.family.length

def QueryWellNamed (n : Names) : Universe.Query → Prop
  | .atom atom => AtomWellNamed n atom
  | .neg query => QueryWellNamed n query
  | .conj left right | .disj left right => QueryWellNamed n left ∧ QueryWellNamed n right

@[simp] theorem head_tagged (tag : Tag) (args : List Sx) :
    head (tagged tag args) = some (tag, args) := by
  have parsed : Tag.spelling.parse tag.text = some tag :=
    Tag.spelling.parse_text Tag.spelling_complete Tag.spelling_nodup tag
  simp [head, tagged, parsed]

@[simp] theorem decode_encodeNat (n : Nat) : decodeNat (encodeNat n) = .ok n := by
  simp [decodeNat, encodeNat, toString]

/-- Bounds are essential: P0 encodes an out-of-range index as the empty atom. -/
theorem decode_encodeIdx (table : List String) (unique : table.Nodup)
    (what : String) (i : Nat) (bound : i < table.length) :
    decodeIdx table what (encodeIdx table i) = .ok i := by
  simp [decodeIdx, encodeIdx, List.getD_eq_getElem?_getD, unique, bound]

theorem decode_encodeWord {α : Type} (sp : Spelling α)
    (complete : ∀ a, a ∈ sp.all) (unique : (sp.all.map sp.text).Nodup)
    (what : String) (a : α) : decodeWord sp what (.atom (sp.text a)) = .ok a := by
  simp [decodeWord, sp.parse_text complete unique]

theorem decodeList_map_of (encode : α → Sx) (decode : Sx → Except Error α)
    (p : α → Prop) (roundtrip : ∀ a, p a → decode (encode a) = .ok a)
    (values : List α) (valid : ∀ a ∈ values, p a) :
    decodeList decode (values.map encode) = .ok values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at valid
      simp [decodeList, roundtrip value valid.1, ih valid.2]

theorem decode_encodeInput (n : Names) (unique : UniqueNames n)
    (input : DataId × VersionId) (valid : InputWellNamed n input) :
    decodeInput n (encodeInput n input) = .ok input := by
  rcases input with ⟨⟨data⟩, ⟨version⟩⟩
  simp [encodeInput, decodeInput, decode_encodeIdx n.data unique.2.2.2.2.2.2.1
    "data" data valid]

theorem decode_encodeInputs (n : Names) (unique : UniqueNames n)
    (inputs : List (DataId × VersionId)) (valid : ∀ input ∈ inputs, InputWellNamed n input) :
    decodeInputs n (encodeInputs n inputs) = .ok inputs := by
  simp only [encodeInputs, decodeInputs, head_tagged]
  exact decodeList_map_of _ _ _ (decode_encodeInput n unique) inputs valid

theorem decode_encodeBody (n : Names) (unique : UniqueNames n)
    (event : Event) (valid : EventWellNamed n event) :
    decodeBody n (encodeBody n event) = .ok event := by
  rcases unique with ⟨ue, ua, up, ur, uc, us, ud, uf, uw⟩
  have hi := decode_encodeIdx
  cases event with
  | commitPlan actor plan version =>
      rcases actor with ⟨actor⟩; rcases plan with ⟨plan⟩; rcases version with ⟨version⟩
      simp [encodeBody, decodeBody, hi _ ua _ actor valid.1, hi _ up _ plan valid.2]
  | access actor data purpose =>
      rcases actor with ⟨actor⟩; rcases data with ⟨data⟩
      simp [encodeBody, decodeBody, hi _ ua _ actor valid.1, hi _ ud _ data valid.2,
        decode_encodeWord AccessPurpose.spelling AccessPurpose.spelling_complete
          AccessPurpose.spelling_nodup]
  | run run plan version inputs family =>
      rcases run with ⟨run⟩; rcases plan with ⟨plan⟩; rcases version with ⟨version⟩
      rcases family with ⟨family⟩
      simp [encodeBody, decodeBody, hi _ ur _ run valid.1, hi _ up _ plan valid.2.1,
        decode_encodeInputs n ⟨ue, ua, up, ur, uc, us, ud, uf, uw⟩ inputs valid.2.2.1,
        hi _ uf _ family valid.2.2.2]
  | result run outcome =>
      rcases run with ⟨run⟩
      simp [encodeBody, decodeBody, hi _ ur _ run valid]
  | assert claim witness =>
      rcases claim with ⟨claim⟩; rcases witness with ⟨witness⟩
      simp [encodeBody, decodeBody, hi _ uc _ claim valid.1, hi _ uw _ witness valid.2]
  | retract source =>
      rcases source with ⟨source⟩
      simp [encodeBody, decodeBody, hi _ us _ source valid]
  | updateData data version =>
      rcases data with ⟨data⟩; rcases version with ⟨version⟩
      simp [encodeBody, decodeBody, hi _ ud _ data valid]

theorem decode_encodeStamped (n : Names) (unique : UniqueNames n)
    (event : Stamped) (valid : StampedWellNamed n event) :
    decodeStamped n (encodeStamped n event) = .ok event := by
  rcases event with ⟨⟨id⟩, event⟩
  simp [encodeStamped, decodeStamped, decode_encodeIdx n.event unique.1 "event" id valid.1,
    decode_encodeBody n unique event valid.2]

private theorem decode_data_indices (n : Names) (unique : n.data.Nodup)
    (data : List DataId) (valid : ∀ d ∈ data, d.index < n.data.length) :
    decodeList (decodeIdx n.data "data") (data.map fun d => encodeIdx n.data d.index) =
      .ok (data.map DataId.index) := by
  induction data with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at valid
      simp [decodeList, decode_encodeIdx _ unique _ d.index valid.1, ih valid.2]

theorem decode_encodeQuery (n : Names) (unique : UniqueNames n)
    (query : Universe.Query) (valid : QueryWellNamed n query) :
    decodeQuery n (encodeQuery n query) = .ok query := by
  induction query with
  | atom atom =>
      cases atom with
      | predictable => rfl
      | runPrecommitted run =>
          rcases run with ⟨run⟩
          simp [encodeQuery, tagged, decodeQuery, Tag.text,
            decode_encodeIdx _ unique.2.2.2.1 _ run valid]
      | familyCountAtMost family bound =>
          rcases family with ⟨family⟩
          simp [encodeQuery, tagged, decodeQuery, Tag.text,
            decode_encodeIdx _ unique.2.2.2.2.2.2.2.1 _ family valid]
      | splitSelection selection test =>
          simp [encodeQuery, tagged, decodeQuery, Tag.text,
            decode_data_indices n unique.2.2.2.2.2.2.1 selection valid.1,
            decode_data_indices n unique.2.2.2.2.2.2.1 test valid.2,
            List.map_map, Function.comp_def]
  | neg query ih => simp [encodeQuery, tagged, decodeQuery, Tag.text, ih valid]
  | conj left right il ir =>
      simp [encodeQuery, tagged, decodeQuery, Tag.text, il valid.1, ir valid.2]
  | disj left right il ir =>
      simp [encodeQuery, tagged, decodeQuery, Tag.text, il valid.1, ir valid.2]

end Lara.Process.InquiryProcessWire
