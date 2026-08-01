/-
Mechanized abstract strict-certificate backend (`Lara.Strict`).  Mathematical
acceptance remains proposition-valued, while every backend also supplies a
Boolean replay and proves it adequate.  Backends are indexed by the source
canonicalizer, preventing a registry constructed for one normalization policy
from being used by another.  A `Backend` is a theory-free *core*, fixed per
registered `(name, version)` identity: its consequence/acceptance/replay
operate on an explicit full consulted context `Γ = Δ ++ T` (the Haskell
adapter's `free = premises ++ theory`), where the digest-addressed theory `T`
enters only as *data* supplied at resolution time — digest resolution cannot
introduce behavior.  Every core also reports its certificate dependencies
(`uses`, spec §5 `uses_beta`) and proves obligation 4 as three laws over the
full context (result 3 certificate half): coverage (`uses_covers` — replay
consults no premise *or theory entry* outside the report), validity
(`uses_valid` — every reported slot names an entry of the consulted
context), and semantic accounting (`uses_account` — an accepted
certificate's conclusion follows from just the reported entries).  Because
theory is data in the quantified context, coverage specializes to
`replay_theory_covers`: swapping the resolved theory is observable only
through reported theory slots, so a core cannot consult a digest-selected
entry without reporting it.  The ND adapter discharges the laws via
`infer_agree`, `fv_in_range`, and `nd_relevance`, with
`ndUses_eq_infer_deps` tying the report to the running checker's dependency
output.
-/

import Lara.Prop
import Lara.ND
import Lara.Certificate
import Std.Data.String.ToNat
import Init.Data.String.Lemmas.Basic

namespace Lara.Strict

/-- Source propositions at the strict seam. -/
abbrev SourceProp := Lara.Atom

/-- The sublist of `Γ` addressed by dependency slots `ids`, order- and
multiplicity-preserving.  The load-bearing callers pass the *full consulted
context* `Γ = Δ ++ T` (submitted premise encodings, then the resolved theory
data), so a slot below the premise count selects a premise and a slot at or
beyond it selects the corresponding theory entry; only a slot at or beyond
`Γ.length` selects nothing. -/
def selectSlots {α : Type _} (Γ : List α) (ids : List Nat) : List α :=
  ids.filterMap (fun i => Γ[i]?)

theorem mem_selectSlots {α : Type _} {Δ : List α} {ids : List Nat} {a : α} :
    a ∈ selectSlots Δ ids ↔ ∃ i, i ∈ ids ∧ Δ[i]? = some a := by
  simp [selectSlots, List.mem_filterMap]

/-- Slot selection commutes with encoding the premise list. -/
theorem selectSlots_map {α β : Type _} (f : α → β) (Δ : List α)
    (ids : List Nat) : selectSlots (Δ.map f) ids = (selectSlots Δ ids).map f := by
  induction ids with
  | nil => rfl
  | cons i ids ih =>
    cases h : Δ[i]? with
    | none =>
      simp [selectSlots, h]
      simpa [selectSlots] using ih
    | some a =>
      simp [selectSlots, h]
      simpa [selectSlots] using ih

/-- A registered strict backend **core** for one fixed source canonicalizer.
One core is registered per exact `(name, version)` identity; it carries *no*
theory of its own.  Its consequence/acceptance/replay operate on the explicit
**full consulted context** `Γ = Δ ++ T` (submitted premise encodings in
front, then the digest-resolved theory data — exactly the Haskell adapter's
`free = premises ++ theory`).  The dependency laws range over that full
context, so the core cannot consult a premise *or a resolved theory entry*
without the coverage law seeing it; whatever a core consults beyond `Γ` is
extensionally constant — part of the backend identity `β` named by the
assurance triple, not hidden data.  The caller-facing closed forms `models`
/ `accepts` / `replay` (resolved theory appended internally) are derived
below. -/
structure Backend (canon : String → String) where
  /-- Backend-private formula type. -/
  Form : Type
  /-- Source encoding. -/
  enc : SourceProp → Form
  /-- Encoding identifies exactly canonical source identity. -/
  enc_iff : ∀ p q, enc p = enc q ↔ Lara.equiv canon p q
  /-- Mathematical consequence over an explicit full context. -/
  modelsFull : List Form → Form → Prop
  /-- Proposition-level acceptance of the exact submitted certificate, over
  an explicit full context. -/
  acceptsFull : Lara.Support.CertRef → List Form → Form → Prop
  /-- Executable replay of the exact submitted certificate, over an explicit
  full context. -/
  replayFull : Lara.Support.CertRef → List Form → Form → Bool
  /-- Replay is adequate for mathematical acceptance. -/
  replayFull_iff : ∀ κ Γ φ, replayFull κ Γ φ = true ↔ acceptsFull κ Γ φ
  /-- Certificate soundness. -/
  soundFull : ∀ κ Γ φ, acceptsFull κ Γ φ → modelsFull Γ φ
  /-- Reported certificate dependencies (spec §5 `uses_beta : Cert_beta → Set
  Dependency`): dependency slots as indices into the full consulted context.
  A function of the certificate alone; a slot below the submitted premise
  count names a premise, and a slot at or beyond it names entry
  `i - Δ.length` of the digest-addressed theory. -/
  uses : Lara.Support.CertRef → List Nat
  /-- Obligation 4, coverage clause (decision doc §2: "every free premise or
  theory entry consulted by `κ` is returned by `uses_beta(κ)`"), in
  extensional form over the full context: replay consults nothing outside
  the report — two consulted contexts (premises *and* theory entries) that
  agree on every reported slot replay identically. -/
  uses_covers : ∀ κ Γ Γ' φ, (∀ i, i ∈ uses κ → Γ[i]? = Γ'[i]?) →
    replayFull κ Γ φ = replayFull κ Γ' φ
  /-- Obligation 4, validity clause (decision doc §2: "every returned
  dependency names a declared premise slot or an entry in the
  digest-addressed `T`"): on acceptance every reported slot is in range of
  the full consulted context. -/
  uses_valid : ∀ κ Γ φ, acceptsFull κ Γ φ → ∀ i, i ∈ uses κ → i < Γ.length
  /-- Semantic dependency accounting (spec §9 result 3): an accepted
  certificate's conclusion is a consequence of just the reported entries of
  the full consulted context — selected premises and selected theory entries
  alike; no free strict assumption is hidden. -/
  uses_account : ∀ κ Γ φ, acceptsFull κ Γ φ →
    modelsFull (selectSlots Γ (uses κ)) φ

namespace Backend

variable {canon : String → String} (B : Backend canon)

/-- Caller-facing consequence of the core resolved with theory data `T`:
the resolved theory is appended internally. -/
def models (T : List B.Form) (Δ : List B.Form) (φ : B.Form) : Prop :=
  B.modelsFull (Δ ++ T) φ

/-- Caller-facing acceptance of the core resolved with theory data `T`. -/
def accepts (T : List B.Form) (κ : Lara.Support.CertRef) (Δ : List B.Form)
    (φ : B.Form) : Prop :=
  B.acceptsFull κ (Δ ++ T) φ

/-- Caller-facing replay of the core resolved with theory data `T`. -/
def replay (T : List B.Form) (κ : Lara.Support.CertRef) (Δ : List B.Form)
    (φ : B.Form) : Bool :=
  B.replayFull κ (Δ ++ T) φ

theorem replay_iff (T : List B.Form) (κ : Lara.Support.CertRef)
    (Δ : List B.Form) (φ : B.Form) :
    B.replay T κ Δ φ = true ↔ B.accepts T κ Δ φ :=
  B.replayFull_iff κ (Δ ++ T) φ

theorem sound (T : List B.Form) (κ : Lara.Support.CertRef) (Δ : List B.Form)
    (φ : B.Form) (h : B.accepts T κ Δ φ) : B.models T Δ φ :=
  B.soundFull κ (Δ ++ T) φ h

/-- Closed-form validity: every reported slot of an accepted certificate
names a submitted premise or one of the resolved theory's `T.length`
entries. -/
theorem uses_valid_closed (T : List B.Form) (κ : Lara.Support.CertRef)
    (Δ : List B.Form) (φ : B.Form) (h : B.accepts T κ Δ φ) :
    ∀ i, i ∈ B.uses κ → i < Δ.length + T.length := by
  intro i hi
  simpa [List.length_append] using
    B.uses_valid κ (Δ ++ T) φ h i hi

/-- **Theory coverage.** Replay consults the resolved theory only at the
reported theory slots: resolving the same core with theories that agree on
every reported theory slot replays identically.  `uses_covers` specialized
along the premise/theory split of the full context — since the core is fixed
per backend identity and a digest resolves only to theory *data*, a
certificate cannot consult a digest-selected entry its report does not
name. -/
theorem replay_theory_covers (κ : Lara.Support.CertRef) (Δ : List B.Form)
    {T T' : List B.Form} (φ : B.Form)
    (hag : ∀ i, i ∈ B.uses κ → Δ.length ≤ i →
      T[i - Δ.length]? = T'[i - Δ.length]?) :
    B.replay T κ Δ φ = B.replay T' κ Δ φ := by
  apply B.uses_covers
  intro i hi
  rcases Nat.lt_or_ge i Δ.length with hlt | hge
  · rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
  · rw [List.getElem?_append_right hge, List.getElem?_append_right hge,
      hag i hi hge]

/-- A certificate whose report names no theory slot replays identically under
*every* resolved theory: an unreported theory swap cannot change
acceptance. -/
theorem replay_theory_agnostic (κ : Lara.Support.CertRef) (Δ : List B.Form)
    (T T' : List B.Form) (φ : B.Form)
    (hprem : ∀ i, i ∈ B.uses κ → i < Δ.length) :
    B.replay T κ Δ φ = B.replay T' κ Δ φ :=
  B.replay_theory_covers κ Δ φ
    (fun i hi hge => absurd (hprem i hi) (Nat.not_lt.mpr hge))

end Backend

/-- A checked strict step against a core resolved with theory data `T`.  Its
acceptance field stays proposition-level, so the theorem surface speaks about
mathematical acceptance rather than Boolean implementation details. -/
structure StrictJudgment {canon : String → String} (B : Backend canon)
    (T : List B.Form) where
  premises : List SourceProp
  goal : SourceProp
  certificate : Lara.Support.CertRef
  accepted : B.accepts T certificate (premises.map B.enc) (B.enc goal)

namespace StrictJudgment

/-- Construct a proposition-level judgment from raw data accepted by executable
replay.  This is the intended boundary constructor for checker output. -/
def ofReplay {canon : String → String} {B : Backend canon} {T : List B.Form}
    (premises : List SourceProp) (goal : SourceProp)
    (certificate : Lara.Support.CertRef)
    (h : B.replay T certificate (premises.map B.enc) (B.enc goal) = true) :
    StrictJudgment B T where
  premises := premises
  goal := goal
  certificate := certificate
  accepted := (B.replay_iff _ _ _ _).mp h

end StrictJudgment

/-- **Theorem 1 (certified strict-step soundness).** -/
theorem strict_step_sound {canon : String → String} {B : Backend canon}
    {T : List B.Form} (j : StrictJudgment B T) :
    B.models T (j.premises.map B.enc) (B.enc j.goal) :=
  B.sound _ _ _ _ j.accepted

/-! ### Exact source-atom wire encoding

Every field is a canonical UTF-8 byte-length frame, `LEN:PAYLOAD`.  The framed
token stream uses distinct `A`/`N`/`S`/`C`/`L` tags; `L` is followed by a
canonical child count and then the recursively encoded children.
-/

/-- Closed vocabulary for the framed source-atom key. -/
inductive FrameTag where
  | atom | num | str | con | len
deriving DecidableEq, Repr

/-- The single source of truth for frame-tag wire spellings. -/
def FrameTag.toString : FrameTag → String
  | .atom => "A"
  | .num => "N"
  | .str => "S"
  | .con => "C"
  | .len => "L"

def FrameTag.all : List FrameTag := [.atom, .num, .str, .con, .len]

/-- Parse a frame tag from the closed vocabulary. -/
def FrameTag.parse (s : String) : Option FrameTag :=
  FrameTag.all.find? (fun tag => tag.toString = s)

@[simp] theorem FrameTag.parse_toString (tag : FrameTag) :
    FrameTag.parse tag.toString = some tag := by
  cases tag <;> rfl

def charByteSize : List Char → Nat
  | [] => 0
  | c :: cs => c.utf8Size + charByteSize cs

theorem charByteSize_toList (s : String) :
    charByteSize s.toList = s.utf8ByteSize := by
  obtain ⟨cs, rfl⟩ := String.exists_eq_ofList s
  induction cs with
  | nil => simp [charByteSize]
  | cons c cs ih =>
    simp only [String.toList_ofList] at ih
    simp [charByteSize, String.ofList_cons, String.utf8ByteSize_append, ih]

def splitColon : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
      if c = ':' then some ([], rest)
      else do
        let (head, tail) ← splitColon rest
        some (c :: head, tail)

theorem splitColon_append {head tail : List Char} (h : ':' ∉ head) :
    splitColon (head ++ ':' :: tail) = some (head, tail) := by
  induction head with
  | nil => simp [splitColon]
  | cons c cs ih =>
    simp only [List.mem_cons, not_or] at h
    have hc : c ≠ ':' := fun hc => h.1 hc.symm
    simp [splitColon, hc, ih h.2]

def takeUtf8 : Nat → List Char → Option (List Char × List Char)
  | 0, cs => some ([], cs)
  | _ + 1, [] => none
  | n + 1, c :: cs =>
      if c.utf8Size ≤ n + 1 then do
        let (head, tail) ← takeUtf8 (n + 1 - c.utf8Size) cs
        some (c :: head, tail)
      else none

theorem takeUtf8_append (head tail : List Char) :
    takeUtf8 (charByteSize head) (head ++ tail) = some (head, tail) := by
  induction head with
  | nil => simp [charByteSize, takeUtf8]
  | cons c cs ih =>
    have hc : 0 < c.utf8Size := c.utf8Size_pos
    have hle : c.utf8Size ≤ c.utf8Size + charByteSize cs := Nat.le_add_right _ _
    change takeUtf8 (c.utf8Size + charByteSize cs) (c :: (cs ++ tail)) =
      some (c :: cs, tail)
    rw [show c.utf8Size + charByteSize cs =
      (c.utf8Size + charByteSize cs - 1) + 1 by omega]
    simp only [takeUtf8]
    rw [if_pos (by omega)]
    rw [show c.utf8Size + charByteSize cs - 1 + 1 - c.utf8Size =
      charByteSize cs by omega, ih]
    rfl

def frame (s : String) : String :=
  Nat.repr s.utf8ByteSize ++ ":" ++ s

def parseFrame (cs : List Char) : Option (String × List Char) := do
  let (digits, rest) ← splitColon cs
  let ds := String.ofList digits
  let n ← ds.toNat?
  if ds = Nat.repr n then
    let (payload, tail) ← takeUtf8 n rest
    some (String.ofList payload, tail)
  else none

theorem parseFrame_frame (s : String) (tail : List Char) :
    parseFrame ((frame s).toList ++ tail) = some (s, tail) := by
  rw [show (frame s).toList ++ tail =
    (Nat.repr s.utf8ByteSize).toList ++ ':' :: (s.toList ++ tail) by
      simp [frame, String.toList_append]]
  simp only [parseFrame]
  rw [splitColon_append (by
    rw [Nat.toList_repr]
    intro h
    have hd := Nat.isDigit_of_mem_toDigits (b := 10) (n := s.utf8ByteSize)
      (by decide) (by decide) h
    simp at hd)]
  simp only [String.ofList_toList, Nat.toNat?_repr, Option.bind_eq_bind,
    Option.bind_some]
  simp only [if_true]
  rw [← charByteSize_toList, takeUtf8_append]
  simp

def renderFrames : List String → String
  | [] => ""
  | s :: ss => frame s ++ renderFrames ss

def decodeFramesAux : Nat → List Char → Option (List String)
  | 0, [] => some []
  | 0, _ :: _ => none
  | _ + 1, [] => some []
  | fuel + 1, cs@(_ :: _) => do
      let (s, rest) ← parseFrame cs
      some (s :: (← decodeFramesAux fuel rest))

def decodeFrames (s : String) : Option (List String) :=
  decodeFramesAux (s.toList.length + 1) s.toList

theorem decodeFramesAux_render (xs : List String) (fuel : Nat)
    (h : xs.length < fuel) :
    decodeFramesAux fuel (renderFrames xs).toList = some xs := by
  induction xs generalizing fuel with
  | nil =>
    cases fuel <;> simp_all [decodeFramesAux, renderFrames]
  | cons s ss ih =>
    cases fuel with
    | zero => simp at h
    | succ fuel =>
      have hf : ss.length < fuel := by simpa using Nat.lt_of_succ_lt_succ h
      simp only [renderFrames, String.toList_append]
      have hne : (frame s).toList ++ (renderFrames ss).toList ≠ [] := by
        simp [frame, String.toList_append]
      obtain ⟨c, rest, heq⟩ := List.exists_cons_of_ne_nil hne
      have hp := parseFrame_frame s (renderFrames ss).toList
      rw [heq] at hp ⊢
      simp [decodeFramesAux, hp, ih fuel hf]

theorem decodeFrames_render (xs : List String) :
    decodeFrames (renderFrames xs) = some xs := by
  apply decodeFramesAux_render
  induction xs with
  | nil => simp
  | cons s ss ih =>
    simp only [renderFrames, String.toList_append, List.length_append]
    have hcolon : 0 < (frame s).toList.length := by
      simp [frame, String.toList_append]
      have hs : 0 < s.toList.length + 1 := Nat.zero_lt_succ _
      omega
    simp only [List.length_cons]
    omega

theorem frame_length_pos (s : String) : 0 < (frame s).toList.length := by
  simp [frame, String.toList_append]
  have h : 0 < s.toList.length + 1 := Nat.zero_lt_succ _
  omega

mutual
  def sourceTermsToList : Lara.Terms → List Lara.Term
    | .nil => []
    | .cons t ts => t :: sourceTermsToList ts

  def sourceTermsOfList : List Lara.Term → Lara.Terms
    | [] => .nil
    | t :: ts => .cons t (sourceTermsOfList ts)
end

@[simp] theorem sourceTermsOfList_toList (ts : Lara.Terms) :
    sourceTermsOfList (sourceTermsToList ts) = ts := by
  match ts with
  | .nil => rfl
  | .cons t ts =>
      simp [sourceTermsToList, sourceTermsOfList, sourceTermsOfList_toList ts]

mutual
  def atomTermDepth : Lara.Term → Nat
    | .num _ | .str _ => 1
    | .con _ ts => atomTermsDepth ts + 1

  def atomTermsDepth : Lara.Terms → Nat
    | .nil => 0
    | .cons t ts => max (atomTermDepth t) (atomTermsDepth ts)
end

mutual
  def encodeTermKey : Lara.Term → String
    | .num n => renderFrames [FrameTag.num.toString, n]
    | .str s => renderFrames [FrameTag.str.toString, s]
    | .con k ts =>
        renderFrames
          ([FrameTag.con.toString, k, FrameTag.len.toString,
              Nat.repr (sourceTermsToList ts).length] ++
            encodeTermKeys ts)

  def encodeTermKeys : Lara.Terms → List String
    | .nil => []
    | .cons t ts => encodeTermKey t :: encodeTermKeys ts
end

@[simp] theorem encodeTermKeys_eq_map (ts : Lara.Terms) :
    encodeTermKeys ts = (sourceTermsToList ts).map encodeTermKey := by
  match ts with
  | .nil => rfl
  | .cons t ts =>
      simp [encodeTermKeys, sourceTermsToList, encodeTermKeys_eq_map ts]

def encodeAtomKey : Lara.Atom → String
  | .atom p ts =>
      renderFrames
        ([FrameTag.atom.toString, p, FrameTag.len.toString,
            Nat.repr (sourceTermsToList ts).length] ++
          encodeTermKeys ts)

def decodeTermKeyAux : Nat → String → Option Lara.Term
  | 0, _ => none
  | fuel + 1, key => do
      let fields ← decodeFrames key
      match fields with
      | [tag, payload] =>
          match FrameTag.parse tag with
          | some .num => some (.num payload)
          | some .str => some (.str payload)
          | _ => none
      | conTag :: k :: lenTag :: count :: children =>
          match FrameTag.parse conTag, FrameTag.parse lenTag with
          | some .con, some .len =>
              let n ← count.toNat?
              if count = Nat.repr n then pure () else none
              if children.length = n then
                return .con k
                  (sourceTermsOfList (← children.mapM (decodeTermKeyAux fuel)))
              else none
          | _, _ => none
      | _ => none

def decodeAtomKey (key : String) : Option Lara.Atom := do
  let fields ← decodeFrames key
  match fields with
  | atomTag :: p :: lenTag :: count :: children =>
      match FrameTag.parse atomTag, FrameTag.parse lenTag with
      | some .atom, some .len =>
          let n ← count.toNat?
          if count = Nat.repr n then pure () else none
          if children.length = n then
            return .atom p
              (sourceTermsOfList (← children.mapM
                (decodeTermKeyAux (key.toList.length + 1))))
          else none
      | _, _ => none
  | _ => none

mutual
  theorem decodeTermKeyAux_encode (t : Lara.Term) (fuel : Nat)
      (h : atomTermDepth t < fuel) :
      decodeTermKeyAux fuel (encodeTermKey t) = some t := by
    cases t with
    | num n =>
      cases fuel with
      | zero => simp [atomTermDepth] at h
      | succ fuel =>
        simp [decodeTermKeyAux, encodeTermKey, decodeFrames_render]
    | str s =>
      cases fuel with
      | zero => simp [atomTermDepth] at h
      | succ fuel =>
        simp [decodeTermKeyAux, encodeTermKey, decodeFrames_render]
    | con k ts =>
      cases fuel with
      | zero => simp [atomTermDepth] at h
      | succ fuel =>
        have ht : atomTermsDepth ts < fuel := by
          simpa [atomTermDepth] using Nat.lt_of_succ_lt_succ h
        simp [decodeTermKeyAux, encodeTermKey, decodeFrames_render,
          Nat.toNat?_repr]
        rw [show (decodeTermKeyAux fuel ∘ encodeTermKey) =
          (fun t => decodeTermKeyAux fuel (encodeTermKey t)) by rfl,
          decodeTermKeys_encode ts fuel ht]
        simp

  theorem decodeTermKeys_encode (ts : Lara.Terms) (fuel : Nat)
      (h : atomTermsDepth ts < fuel) :
      (sourceTermsToList ts).mapM
          (fun t => decodeTermKeyAux fuel (encodeTermKey t)) =
        some (sourceTermsToList ts) := by
    cases ts with
    | nil => rfl
    | cons t ts =>
      have ht : atomTermDepth t < fuel :=
        Nat.lt_of_le_of_lt (Nat.le_max_left ..) h
      have hts : atomTermsDepth ts < fuel :=
        Nat.lt_of_le_of_lt (Nat.le_max_right ..) h
      simp [sourceTermsToList, decodeTermKeyAux_encode t fuel ht,
        decodeTermKeys_encode ts fuel hts]
end

def payloadChars : List String → Nat
  | [] => 0
  | s :: ss => s.toList.length + payloadChars ss

theorem payloadChars_le_renderFrames (xs : List String) :
    payloadChars xs ≤ (renderFrames xs).toList.length := by
  induction xs with
  | nil => simp [payloadChars, renderFrames]
  | cons s ss ih =>
    simp only [payloadChars, renderFrames, String.toList_append, List.length_append]
    have hf : s.toList.length ≤ (frame s).toList.length := by
      simp [frame, String.toList_append]
      omega
    omega

@[simp] theorem payloadChars_append (xs ys : List String) :
    payloadChars (xs ++ ys) = payloadChars xs + payloadChars ys := by
  induction xs with
  | nil => simp [payloadChars]
  | cons x xs ih => simp [payloadChars, ih, Nat.add_assoc]

mutual
  theorem atomTermDepth_le_key_length (t : Lara.Term) :
      atomTermDepth t ≤ (encodeTermKey t).toList.length := by
    match t with
    | .num n =>
        have hp := frame_length_pos FrameTag.num.toString
        simp [atomTermDepth, encodeTermKey, renderFrames, String.toList_append]
        omega
    | .str s =>
        have hp := frame_length_pos FrameTag.str.toString
        simp [atomTermDepth, encodeTermKey, renderFrames, String.toList_append]
        omega
    | .con k ts =>
        have hts := atomTermsDepth_le_keys_length ts
        have hrender := payloadChars_le_renderFrames
          ([FrameTag.con.toString, k, FrameTag.len.toString,
              Nat.repr (sourceTermsToList ts).length] ++ encodeTermKeys ts)
        have hprefix : 0 <
            payloadChars [FrameTag.con.toString, k, FrameTag.len.toString,
              Nat.repr (sourceTermsToList ts).length] := by
          simp [payloadChars, FrameTag.toString]
          omega
        simp only [atomTermDepth, encodeTermKey]
        have happ := payloadChars_append
          [FrameTag.con.toString, k, FrameTag.len.toString,
            Nat.repr (sourceTermsToList ts).length] (encodeTermKeys ts)
        omega

  theorem atomTermsDepth_le_keys_length (ts : Lara.Terms) :
      atomTermsDepth ts ≤ payloadChars (encodeTermKeys ts) := by
    match ts with
    | .nil => exact Nat.le_refl 0
    | .cons t ts =>
        have ht := atomTermDepth_le_key_length t
        have hts := atomTermsDepth_le_keys_length ts
        simp only [atomTermsDepth, encodeTermKeys, payloadChars]
        exact Nat.max_le.mpr
          ⟨Nat.le_add_right_of_le ht, Nat.le_add_left_of_le hts⟩
end

theorem decodeAtomKey_encodeAtomKey (a : Lara.Atom) :
    decodeAtomKey (encodeAtomKey a) = some a := by
  cases a with
  | atom p ts =>
    have hdepth : atomTermsDepth ts <
        (encodeAtomKey (.atom p ts)).toList.length + 1 := by
      have hle := atomTermsDepth_le_keys_length ts
      have hr := payloadChars_le_renderFrames
        ([FrameTag.atom.toString, p, FrameTag.len.toString,
            Nat.repr (sourceTermsToList ts).length] ++ encodeTermKeys ts)
      have happ := payloadChars_append
        [FrameTag.atom.toString, p, FrameTag.len.toString,
          Nat.repr (sourceTermsToList ts).length] (encodeTermKeys ts)
      simp only [encodeAtomKey]
      omega
    simp [decodeAtomKey, encodeAtomKey, decodeFrames_render,
      Nat.toNat?_repr]
    have hdepth' : atomTermsDepth ts <
        (renderFrames
          ([FrameTag.atom.toString, p, FrameTag.len.toString,
              Nat.repr (sourceTermsToList ts).length] ++
            (sourceTermsToList ts).map encodeTermKey)).toList.length + 1 := by
      simpa [encodeAtomKey, encodeTermKeys_eq_map] using hdepth
    have hmap := decodeTermKeys_encode ts
      ((renderFrames
        ([FrameTag.atom.toString, p, FrameTag.len.toString,
            Nat.repr (sourceTermsToList ts).length] ++
          (sourceTermsToList ts).map encodeTermKey)).toList.length + 1) hdepth'
    change ((List.mapM
      (fun t => decodeTermKeyAux
        ((renderFrames
          ([FrameTag.atom.toString, p, FrameTag.len.toString,
              Nat.repr (sourceTermsToList ts).length] ++
            (sourceTermsToList ts).map encodeTermKey)).toList.length + 1)
        (encodeTermKey t))
      (sourceTermsToList ts)).bind
        (fun xs => some (Lara.Atom.atom p (sourceTermsOfList xs)))) =
      some (Lara.Atom.atom p ts)
    rw [hmap]
    simp

theorem encodeAtomKey_injective : Function.Injective encodeAtomKey := by
  intro a b h
  have ha := decodeAtomKey_encodeAtomKey a
  have hb := decodeAtomKey_encodeAtomKey b
  rw [h] at ha
  rw [ha] at hb
  exact Option.some.inj hb

def ndEnc (canon : String → String) (p : SourceProp) : Lara.ND.Formula :=
  .atom (encodeAtomKey (Lara.nf canon p))

theorem ndEnc_iff (canon : String → String) (p q : SourceProp) :
    ndEnc canon p = ndEnc canon q ↔ Lara.equiv canon p q := by
  simp only [ndEnc, Lara.equiv, Lara.ND.Formula.atom.injEq]
  exact ⟨fun h => encodeAtomKey_injective h, congrArg encodeAtomKey⟩

/-! ### Executable ND replay adapter -/

def ndModels (Δ : List Lara.ND.Formula) (φ : Lara.ND.Formula) : Prop :=
  ∀ v : String → Bool,
    (∀ ψ, ψ ∈ Δ → Lara.ND.satisfies v ψ) → Lara.ND.satisfies v φ

/-- Symbolic wire payload for the ND certificate `hyp 0`. -/
def ndHypZero : Lara.Support.SExpr :=
  .list [.atom "hyp", .atom "0"]

/-- Acceptance means that the exact submitted symbolic certificate decodes and
has the requested type in the submitted free context. -/
def ndAccepts (κ : Lara.Support.CertRef) (Δ : List Lara.ND.Formula)
    (φ : Lara.ND.Formula) : Prop :=
  ∃ e, Lara.ND.decodeCert κ.payload = some e ∧ Lara.ND.HasType Δ e φ

/-- Decode and infer the exact submitted certificate; no proof search occurs. -/
def ndReplay (κ : Lara.Support.CertRef) (Δ : List Lara.ND.Formula)
    (φ : Lara.ND.Formula) : Bool :=
  match Lara.ND.decodeCert κ.payload with
  | none => false
  | some e =>
      match Lara.ND.infer Δ [] e with
      | some (conclusion, _) => conclusion == φ
      | none => false

theorem ndReplay_iff (κ : Lara.Support.CertRef) (Δ : List Lara.ND.Formula)
    (φ : Lara.ND.Formula) :
    ndReplay κ Δ φ = true ↔ ndAccepts κ Δ φ := by
  constructor
  · intro h
    simp only [ndReplay] at h
    cases hd : Lara.ND.decodeCert κ.payload with
    | none => simp [hd] at h
    | some e =>
      cases hi : Lara.ND.infer Δ [] e with
      | none => simp [hd, hi] at h
      | some result =>
        obtain ⟨conclusion, deps⟩ := result
        have hc : conclusion = φ := by simpa [hd, hi] using h
        exact ⟨e, hd, hc ▸ (by simpa using Lara.ND.infer_sound [] e conclusion deps hi)⟩
  · rintro ⟨e, hd, ht⟩
    obtain ⟨deps, hi⟩ := Lara.ND.infer_complete (free := Δ) [] e φ (by simpa using ht)
    simp [ndReplay, hd, hi]

/-- Reported dependency slots of an ND certificate: the free de Bruijn
variables of the decoded proof term.  A function of the certificate alone; an
undecodable certificate reports nothing (it is never accepted). -/
def ndUses (κ : Lara.Support.CertRef) : List Nat :=
  match Lara.ND.decodeCert κ.payload with
  | none => []
  | some e => Lara.ND.fv e

/-- **Dependency accounting for the ND adapter (result 10, exactness half).**
An accepted certificate's conclusion already follows from just the premises
its free-variable report selects — `nd_relevance` at the backend interface. -/
theorem ndUses_account (κ : Lara.Support.CertRef)
    (Δ : List Lara.ND.Formula) (φ : Lara.ND.Formula)
    (hacc : ndAccepts κ Δ φ) :
    ndModels (selectSlots Δ (ndUses κ)) φ := by
  obtain ⟨e, hdec, ht⟩ := hacc
  have hu : ndUses κ = Lara.ND.fv e := by simp [ndUses, hdec]
  intro v hv
  refine Lara.ND.nd_relevance ht v ?_
  intro i ψ hi hlook
  refine hv ψ ?_
  rw [hu]
  exact mem_selectSlots.mpr
    ⟨i, hi, by rw [← Lara.ND.lookup_eq_getElem?]; exact hlook⟩

/-- **Obligation 4, coverage (ND).** Replay consults the context only at the
reported slots: contexts agreeing there replay identically
(`infer_agree` at the certificate boundary; no arity hypothesis needed). -/
theorem ndReplay_agree (κ : Lara.Support.CertRef)
    {Δ Δ' : List Lara.ND.Formula} (φ : Lara.ND.Formula)
    (hag : ∀ i, i ∈ ndUses κ → Δ[i]? = Δ'[i]?) :
    ndReplay κ Δ φ = ndReplay κ Δ' φ := by
  cases hdec : Lara.ND.decodeCert κ.payload with
  | none => simp [ndReplay, hdec]
  | some e =>
    have hu : ndUses κ = Lara.ND.fv e := by simp [ndUses, hdec]
    have hinf := Lara.ND.infer_agree (free := Δ) (free' := Δ') [] e (by
      intro j hj
      rw [Lara.ND.lookup_eq_getElem?, Lara.ND.lookup_eq_getElem?]
      exact hag j (by rw [hu]; simpa using hj))
    simp [ndReplay, hdec, hinf]

/-- **Obligation 4, validity (ND).** An accepted certificate's reported slots
all name entries of the consulted context (`fv_in_range`). -/
theorem ndUses_valid (κ : Lara.Support.CertRef)
    (Γ : List Lara.ND.Formula) (φ : Lara.ND.Formula)
    (hacc : ndAccepts κ Γ φ) : ∀ i, i ∈ ndUses κ → i < Γ.length := by
  obtain ⟨e, hdec, ht⟩ := hacc
  have hu : ndUses κ = Lara.ND.fv e := by simp [ndUses, hdec]
  intro i hi
  exact Lara.ND.fv_in_range ht i (hu ▸ hi)

/-- The reported slots are exactly what the running checker computes: on a
decodable certificate accepted by `infer`, `ndUses` is the algorithm's
dependency output (`infer_deps_eq_fv` at the certificate boundary). -/
theorem ndUses_eq_infer_deps {κ : Lara.Support.CertRef}
    {Δ : List Lara.ND.Formula} {e : Lara.ND.Cert} {φ : Lara.ND.Formula}
    {ds : List Nat} (hdec : Lara.ND.decodeCert κ.payload = some e)
    (hinf : Lara.ND.infer Δ [] e = some (φ, ds)) :
    ndUses κ = ds := by
  have hfv := Lara.ND.infer_deps_eq_fv e φ ds hinf
  simp [ndUses, hdec, hfv]

/-- The one fixed ND backend core.  A registered digest resolves only to
theory *data* (ND-encoded entries) that the derived closed forms append after
the caller-supplied premise encodings — digest resolution never changes the
core. -/
def ndBackend (canon : String → String) : Backend canon where
  Form := Lara.ND.Formula
  enc := ndEnc canon
  enc_iff := ndEnc_iff canon
  modelsFull := ndModels
  acceptsFull := ndAccepts
  replayFull := ndReplay
  replayFull_iff := ndReplay_iff
  soundFull := by
    rintro κ Γ φ ⟨e, _, ht⟩
    exact Lara.ND.nd_sound ht
  uses := ndUses
  uses_covers := fun κ Γ Γ' φ hag => ndReplay_agree κ φ hag
  uses_valid := ndUses_valid
  uses_account := ndUses_account

/-- Theorem 1 specialized to the executable ND backend (empty theory). -/
theorem nd_strict_step_sound (j : StrictJudgment (ndBackend id) []) :
    ndModels (j.premises.map (ndBackend id).enc)
      ((ndBackend id).enc j.goal) := by
  have h : ndModels (j.premises.map (ndEnc id) ++ []) (ndEnc id j.goal) :=
    strict_step_sound j
  rwa [List.append_nil] at h

/-! ### Theorem 3 (source non-factivity — the factivity firewall) -/

def nonfactiveAtom : SourceProp := .atom "p" .nil

/-- The accepted symbolic ND identity step `p ⊢ p`, constructed through the
Boolean-to-proposition replay bridge. -/
def nonfactiveJudgment : StrictJudgment (ndBackend id) [] :=
  StrictJudgment.ofReplay [nonfactiveAtom] nonfactiveAtom ⟨ndHypZero⟩ (by
    apply (ndReplay_iff _ _ _).mpr
    exact ⟨.hyp 0, by
      have hz : Lara.ND.decodeNat "0" = some 0 := by
        change Lara.ND.decodeNat (Nat.repr 0) = some 0
        exact Lara.ND.decodeNat_repr 0
      simp [ndHypZero, Lara.ND.decodeCert, Lara.ND.Tag.parse, hz],
      .hyp rfl⟩)

/-- The accepted goal need not be valid without its premise. -/
theorem nd_nonfactive_witness :
    ¬ ndModels [] ((ndBackend id).enc nonfactiveJudgment.goal) := by
  intro h
  have hp : Lara.ND.satisfies (fun _ : String => false)
      ((ndBackend id).enc nonfactiveJudgment.goal) :=
    h (fun _ => false) (fun ψ hψ => nomatch hψ)
  exact Bool.noConfusion hp

/-- There is no uniform premise-free truth projection from checked strict
steps, even when quantified over canonicalizers, backend cores, and resolved
theories. -/
theorem no_truth_projection :
    ¬ ∀ (canon : String → String) (B : Backend canon) (T : List B.Form)
      (j : StrictJudgment B T), B.models T [] (B.enc j.goal) :=
  fun h => nd_nonfactive_witness (h id (ndBackend id) [] nonfactiveJudgment)

/-- Relative soundness and non-factivity side by side. -/
theorem nd_relative_not_absolute :
    ndModels (nonfactiveJudgment.premises.map (ndBackend id).enc)
        ((ndBackend id).enc nonfactiveJudgment.goal)
      ∧ ¬ ndModels [] ((ndBackend id).enc nonfactiveJudgment.goal) :=
  ⟨strict_step_sound nonfactiveJudgment, nd_nonfactive_witness⟩

end Lara.Strict
