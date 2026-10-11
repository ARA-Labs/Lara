import Lara.Process.Universe
import Lara.Driver

/-!
The `process-input 1` S-expression codec.

A document carries a decoded process record (`AraSource`), the coverage bases
the reader admits, the declared universe of events that may have happened
unrecorded, the evaluation limits and the queries. Identifiers are spelled as
names; each namespace declares its names once in the `names` block, and the
decoder interns a name to its position there (`Lara.Process.Rename` shows the
positions cannot matter). Versions and counts are canonical decimals.

Decoding is total. `decodeDocument_canonical` proves the decoder loses nothing:
every document it accepts re-encodes to exactly the S-expression it came from,
so `decode_encode` holds for every decodable document. Text reading and
printing reuse `Lara.Driver`'s executable boundary; their byte-level behavior is
tested, not part of these theorems.
-/

namespace Lara.Process.Wire

open Lara.Process
open Lara.Process.Universe
open Lara.Driver (Sx)

/-! ### Spelling tables -/

/-- A closed vocabulary with its one wire spelling table. -/
structure Spelling (α : Type) where
  all : List α
  text : α → String

namespace Spelling

variable {α : Type} (sp : Spelling α)

def parse (s : String) : Option α := sp.all.find? fun a => sp.text a == s

/-- A table whose spellings are distinct over a complete list parses every
spelling back. -/
theorem parse_text (complete : ∀ a, a ∈ sp.all) (nodup : (sp.all.map sp.text).Nodup) (a : α) :
    sp.parse (sp.text a) = some a := by
  unfold parse
  cases h : sp.all.find? (fun b => sp.text b == sp.text a) with
  | none => exact absurd (List.find?_eq_none.1 h a (complete a)) (by simp)
  | some b =>
      have hb := List.mem_of_find?_eq_some h
      have eq : sp.text b = sp.text a := by simpa using List.find?_some h
      rw [List.inj_on_of_nodup_map nodup hb (complete a) eq]

theorem parse_some {s : String} {a : α} (h : sp.parse s = some a) : sp.text a = s := by
  unfold parse at h; simpa using List.find?_some h

theorem text_injective (complete : ∀ a, a ∈ sp.all) (nodup : (sp.all.map sp.text).Nodup) :
    Function.Injective sp.text := fun a b h => by
  have := sp.parse_text complete nodup a
  rw [h, sp.parse_text complete nodup b] at this
  exact (Option.some.inj this).symm

end Spelling

/-- The structural keywords of the grammar. Forms in different positions may
share a keyword (`event` heads a names table, a record entry and a universe
event); position decides. -/
inductive Tag where
  | processInput | names | event | actor | plan | run | claim | source | data | family | witness
  | record | cutoff | order | coverage | submit | reader | universe | limits | events | completions
  | queries | commitPlan | access | result | assert | retract | updateData | input | inputs | at
  | complete | countBounded | openWorld | declaredPolicy | scope | kinds | actors
  | verdict | audit | runPrecommitted | predictable | splitSelection | familyCountAtMost
  | not | and | or | profile | admissible | accepts | guarantee | probes | acceptance
  | processResult | processError | assumptions | admitted | unadmitted | answers | answer
  | holds | fails | history
  deriving DecidableEq, Repr

def Tag.text : Tag → String
  | .processInput => "process-input" | .names => "names" | .event => "event"
  | .actor => "actor" | .plan => "plan" | .run => "run" | .claim => "claim"
  | .source => "source" | .data => "data" | .family => "family" | .witness => "witness"
  | .record => "record" | .cutoff => "cutoff" | .order => "order" | .coverage => "coverage"
  | .submit => "submit" | .reader => "reader" | .universe => "universe" | .limits => "limits"
  | .events => "events" | .completions => "completions" | .queries => "queries"
  | .commitPlan => "commit-plan" | .access => "access" | .result => "result"
  | .assert => "assert" | .retract => "retract" | .updateData => "update-data"
  | .input => "input" | .inputs => "inputs" | .at => "at" | .complete => "complete"
  | .countBounded => "count-bounded" | .openWorld => "open-world"
  | .declaredPolicy => "declared-policy" | .scope => "scope" | .kinds => "kinds"
  | .actors => "actors" | .verdict => "verdict" | .audit => "audit"
  | .runPrecommitted => "run-precommitted" | .predictable => "predictable"
  | .splitSelection => "split-selection" | .familyCountAtMost => "family-count-at-most"
  | .not => "not" | .and => "and" | .or => "or" | .profile => "profile"
  | .admissible => "admissible" | .accepts => "accepts" | .guarantee => "guarantee"
  | .probes => "probes" | .acceptance => "acceptance" | .processResult => "process-result"
  | .processError => "process-error" | .assumptions => "assumptions"
  | .admitted => "admitted" | .unadmitted => "unadmitted" | .answers => "answers"
  | .answer => "answer" | .holds => "holds" | .fails => "fails" | .history => "history"

def Tag.spelling : Spelling Tag where
  all := [.processInput, .names, .event, .actor, .plan, .run, .claim, .source, .data, .family,
    .witness, .record, .cutoff, .order, .coverage, .submit, .reader, .universe, .limits, .events,
    .completions, .queries, .commitPlan, .access, .result, .assert, .retract, .updateData, .input,
    .inputs, .at, .complete, .countBounded, .openWorld, .declaredPolicy, .scope, .kinds, .actors, .verdict,
    .audit, .runPrecommitted, .predictable, .splitSelection, .familyCountAtMost, .not, .and, .or,
    .profile, .admissible, .accepts, .guarantee, .probes, .acceptance, .processResult,
    .processError, .assumptions, .admitted, .unadmitted, .answers, .answer, .holds, .fails,
    .history]
  text := Tag.text

theorem Tag.spelling_complete (t : Tag) : t ∈ Tag.spelling.all := by cases t <;> decide
theorem Tag.spelling_nodup : (Tag.spelling.all.map Tag.spelling.text).Nodup := by decide
theorem Tag.text_injective : Function.Injective Tag.text :=
  Tag.spelling.text_injective Tag.spelling_complete Tag.spelling_nodup

def EventKind.spelling : Spelling EventKind where
  all := [.planCommit, .dataAccess, .analysisRun, .resultProduced, .claimAsserted,
    .sourceRetracted, .dataUpdated]
  text
    | .planCommit => "plan-commit" | .dataAccess => "data-access"
    | .analysisRun => "analysis-run" | .resultProduced => "result-produced"
    | .claimAsserted => "claim-asserted" | .sourceRetracted => "source-retracted"
    | .dataUpdated => "data-updated"

def AccessPurpose.spelling : Spelling AccessPurpose where
  all := [.selection, .evaluation]
  text | .selection => "selection" | .evaluation => "evaluation"

def AdmissionBasis.spelling : Spelling AdmissionBasis where
  all := [.instrumentedLog, .signedAttestation, .authorDeclaration]
  text
    | .instrumentedLog => "instrumented-log" | .signedAttestation => "signed-attestation"
    | .authorDeclaration => "author-declaration"

def EvidenceKind.spelling : Spelling EvidenceKind where
  all := EvidenceKind.all
  text := EvidenceKind.label

/-- The coverage kinds a profile can accept. Version 1 has no declared policy. -/
inductive CoverageKind where
  | complete | countBounded | openWorld
  deriving DecidableEq, Repr

def CoverageKind.of : RecordCoverage Empty → CoverageKind
  | .complete _ => .complete
  | .countBounded _ _ => .countBounded
  | .declaredPolicy _ p => p.elim
  | .openWorld _ => .openWorld

def CoverageKind.spelling : Spelling CoverageKind where
  all := [.complete, .countBounded, .openWorld]
  text | .complete => "complete" | .countBounded => "count-bounded" | .openWorld => "open-world"

def GuaranteeClass.spelling : Spelling GuaranteeClass where
  all := [.fwer, .fdr, .mfdr]
  text | .fwer => "fwer" | .fdr => "fdr" | .mfdr => "mfdr"

def ErrorKind.spelling : Spelling ErrorKind where
  all := ErrorKind.all
  text
    | .sampling => "sampling" | .selection => "selection"
    | .optionalStopping => "optional-stopping" | .misspecification => "misspecification"
    | .measurement => "measurement"

def Acceptance.spelling : Spelling Acceptance where
  all := [.groundedJustified]
  text | .groundedJustified => "grounded-justified"

def Verdict.spelling : Spelling Verdict where
  all := [.inconsistent, .certainTrue, .certainFalse, .unknown]
  text := Verdict.label

theorem EventKind.spelling_complete (a : EventKind) : a ∈ EventKind.spelling.all := by cases a <;> decide
theorem EventKind.spelling_nodup : (EventKind.spelling.all.map EventKind.spelling.text).Nodup := by decide
theorem AccessPurpose.spelling_complete (a : AccessPurpose) : a ∈ AccessPurpose.spelling.all := by
  cases a <;> decide
theorem AccessPurpose.spelling_nodup : (AccessPurpose.spelling.all.map AccessPurpose.spelling.text).Nodup := by
  decide
theorem AdmissionBasis.spelling_complete (a : AdmissionBasis) : a ∈ AdmissionBasis.spelling.all := by
  cases a <;> decide
theorem AdmissionBasis.spelling_nodup :
    (AdmissionBasis.spelling.all.map AdmissionBasis.spelling.text).Nodup := by decide
theorem EvidenceKind.spelling_complete (a : EvidenceKind) : a ∈ EvidenceKind.spelling.all :=
  EvidenceKind.mem_all a
theorem EvidenceKind.spelling_nodup : (EvidenceKind.spelling.all.map EvidenceKind.spelling.text).Nodup := by
  decide
theorem CoverageKind.spelling_complete (a : CoverageKind) : a ∈ CoverageKind.spelling.all := by
  cases a <;> decide
theorem CoverageKind.spelling_nodup : (CoverageKind.spelling.all.map CoverageKind.spelling.text).Nodup := by
  decide
theorem GuaranteeClass.spelling_complete (a : GuaranteeClass) : a ∈ GuaranteeClass.spelling.all := by
  cases a <;> decide
theorem GuaranteeClass.spelling_nodup :
    (GuaranteeClass.spelling.all.map GuaranteeClass.spelling.text).Nodup := by decide
theorem ErrorKind.spelling_complete (a : ErrorKind) : a ∈ ErrorKind.spelling.all := ErrorKind.mem_all a
theorem ErrorKind.spelling_nodup : (ErrorKind.spelling.all.map ErrorKind.spelling.text).Nodup := by decide
theorem Acceptance.spelling_complete (a : Acceptance) : a ∈ Acceptance.spelling.all := by
  cases a; decide
theorem Acceptance.spelling_nodup : (Acceptance.spelling.all.map Acceptance.spelling.text).Nodup := by decide
theorem Verdict.spelling_complete (a : Verdict) : a ∈ Verdict.spelling.all := by cases a <;> decide
theorem Verdict.spelling_nodup : (Verdict.spelling.all.map Verdict.spelling.text).Nodup := by decide

/-! ### Errors -/

/-- Stable refusal categories. Consumers branch on the tag, never the detail. -/
inductive ErrorTag where
  | syntax | malformed | unsupportedVersion | unsupported | limitExceeded | usage | io
  deriving DecidableEq, Repr

def ErrorTag.spelling : Spelling ErrorTag where
  all := [.syntax, .malformed, .unsupportedVersion, .unsupported, .limitExceeded, .usage, .io]
  text
    | .syntax => "syntax" | .malformed => "malformed"
    | .unsupportedVersion => "unsupported-version" | .unsupported => "unsupported"
    | .limitExceeded => "limit-exceeded" | .usage => "usage" | .io => "io"

theorem ErrorTag.spelling_complete (a : ErrorTag) : a ∈ ErrorTag.spelling.all := by cases a <;> decide
theorem ErrorTag.spelling_nodup : (ErrorTag.spelling.all.map ErrorTag.spelling.text).Nodup := by decide

structure Error where
  tag : ErrorTag
  detail : String
  deriving DecidableEq, Repr

/-- Exit codes: `unsupported` and `limit-exceeded` refuse a decoded document
(1); every other refusal is a decode, usage or IO failure (2). -/
def Error.exitCode (e : Error) : UInt32 :=
  match e.tag with
  | .unsupported | .limitExceeded => 1
  | _ => 2

def bad {α : Type} (what : String) : Except Error α := .error ⟨.malformed, what⟩

/-! ### Forms and decoding helpers -/

def tagged (t : Tag) (args : List Sx) : Sx := .list (.atom t.text :: args)

def head (e : Sx) : Option (Tag × List Sx) :=
  match e with
  | .list (.atom s :: args) => (Tag.spelling.parse s).map (·, args)
  | _ => none

theorem head_eq_some {e : Sx} {t : Tag} {args : List Sx} (h : head e = some (t, args)) :
    e = tagged t args := by
  unfold head at h
  split at h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨t', ht, rfl, rfl⟩ := h
    rw [← Tag.spelling.parse_some ht]; rfl
  · cases h

@[simp] theorem bind_ok_iff {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

@[simp] theorem pure_ok_iff {ε α : Type} {a b : α} : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

@[simp] theorem bad_ne_ok {α : Type} {w : String} {a : α} : (bad w : Except Error α) ≠ .ok a := by
  simp [bad]

/-- A total list decoder that keeps order and the first failure. -/
def decodeList {α : Type} (f : Sx → Except Error α) : List Sx → Except Error (List α)
  | [] => .ok []
  | x :: xs => do
    let a ← f x
    let rest ← decodeList f xs
    pure (a :: rest)

theorem decodeList_canonical {α : Type} {f : Sx → Except Error α} {g : α → Sx}
    (hf : ∀ e a, f e = .ok a → g a = e) :
    ∀ {es : List Sx} {as : List α}, decodeList f es = .ok as → as.map g = es
  | [], as, h => by simp only [decodeList, Except.ok.injEq] at h; subst h; rfl
  | x :: xs, as, h => by
      simp only [decodeList, bind_ok_iff, pure_ok_iff] at h
      obtain ⟨a, ha, rest, hr, rfl⟩ := h
      simp only [List.map_cons, hf x a ha, decodeList_canonical hf hr]

/-- A canonical decimal: `toString` of the value it denotes, so `01` and `+1`
are refused. -/
def decodeNat : Sx → Except Error Nat
  | .atom s =>
    match s.toNat? with
    | some n => if toString n = s then .ok n else bad s!"non-canonical number {s}"
    | none => bad s!"expected a number, found {s}"
  | .list _ => bad "expected a number"

def encodeNat (n : Nat) : Sx := .atom (toString n)

theorem decodeNat_canonical {e : Sx} {n : Nat} (h : decodeNat e = .ok n) : encodeNat n = e := by
  unfold decodeNat at h
  split at h
  · split at h
    · split at h
      · cases h; simp only [encodeNat, *]
      · cases h
    · cases h
  · cases h

/-- An atom from a closed vocabulary. -/
def decodeWord {α : Type} (sp : Spelling α) (what : String) : Sx → Except Error α
  | .atom s => match sp.parse s with
    | some a => .ok a
    | none => bad s!"unknown {what} {s}"
  | .list _ => bad s!"expected a {what}"

theorem decodeWord_canonical {α : Type} {sp : Spelling α} {what : String} {e : Sx} {a : α}
    (h : decodeWord sp what e = .ok a) : Sx.atom (sp.text a) = e := by
  unfold decodeWord at h
  split at h
  · split at h
    · cases h; rw [sp.parse_some ‹_›]
    · cases h
  · cases h

/-- A free text atom: a file, an entry or a query name. -/
def decodeText : Sx → Except Error String
  | .atom s => .ok s
  | .list _ => bad "expected an atom"

theorem decodeText_canonical {e : Sx} {s : String} (h : decodeText e = .ok s) : Sx.atom s = e := by
  unfold decodeText at h; split at h <;> cases h; rfl

/-! ### Identifier tables -/

/-- The declared names of every identifier namespace. Strings are correct here:
this is the decode boundary, and the symbolic core only sees positions. -/
structure Names where
  event : List String
  actor : List String
  plan : List String
  run : List String
  claim : List String
  source : List String
  data : List String
  family : List String
  witness : List String
  deriving DecidableEq, Repr

/-- The position of a declared name. An undeclared name is refused. -/
def decodeIdx (table : List String) (what : String) : Sx → Except Error Nat
  | .atom s =>
    if table.idxOf s < table.length then .ok (table.idxOf s)
    else bad s!"undeclared {what} name {s}"
  | .list _ => bad s!"expected a {what} name"

def encodeIdx (table : List String) (i : Nat) : Sx := .atom (table.getD i "")

theorem decodeIdx_canonical {table : List String} {what : String} {e : Sx} {i : Nat}
    (h : decodeIdx table what e = .ok i) : encodeIdx table i = e := by
  unfold decodeIdx at h
  split at h
  · split at h
    · cases h
      simp only [encodeIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ‹_›,
        Option.getD_some, List.getElem_idxOf]
    · cases h
  · cases h

/-- One names table: `(TAG NAME ...)`, without duplicates. -/
def decodeTable (t : Tag) (e : Sx) : Except Error (List String) :=
  match head e with
    | some (t', args) =>
      if t' = t then do
        let names ← decodeList decodeText args
        if names.Nodup then .ok names else bad s!"duplicate {t.text} name"
      else bad s!"expected the {t.text} names"
    | none => bad s!"expected the {t.text} names"

def encodeTable (t : Tag) (names : List String) : Sx := tagged t (names.map Sx.atom)

theorem decodeTable_canonical {t : Tag} {e : Sx} {names : List String}
    (h : decodeTable t e = .ok names) : encodeTable t names = e := by
  unfold decodeTable at h
  split at h
  · rename_i t' args he
    split at h
    · subst_vars
      simp only [bind_ok_iff] at h
      obtain ⟨ns, hns, hn⟩ := h
      split at hn
      · cases hn
        rw [head_eq_some he, encodeTable, decodeList_canonical (fun _ _ => decodeText_canonical) hns]
      · cases hn
    · cases h
  · cases h

def decodeNames (e : Sx) : Except Error Names :=
  match head e with
  | some (.names, [ev, ac, pl, ru, cl, so, da, fa, wi]) => do
    pure ⟨← decodeTable .event ev, ← decodeTable .actor ac, ← decodeTable .plan pl,
      ← decodeTable .run ru, ← decodeTable .claim cl, ← decodeTable .source so,
      ← decodeTable .data da, ← decodeTable .family fa, ← decodeTable .witness wi⟩
  | _ => bad "expected the names block"

def encodeNames (n : Names) : Sx :=
  tagged .names [encodeTable .event n.event, encodeTable .actor n.actor, encodeTable .plan n.plan,
    encodeTable .run n.run, encodeTable .claim n.claim, encodeTable .source n.source,
    encodeTable .data n.data, encodeTable .family n.family, encodeTable .witness n.witness]

theorem decodeNames_canonical {e : Sx} {n : Names} (h : decodeNames e = .ok n) :
    encodeNames n = e := by
  unfold decodeNames at h
  split at h
  · rename_i ev ac pl ru cl so da fa wi he
    simp only [bind_ok_iff, pure_ok_iff] at h
    obtain ⟨a, ha, b, hb, c, hc, d, hd, f, hf, g, hg, i, hi, j, hj, k, hk, rfl⟩ := h
    rw [head_eq_some he]
    simp only [encodeNames, decodeTable_canonical ha, decodeTable_canonical hb,
      decodeTable_canonical hc, decodeTable_canonical hd, decodeTable_canonical hf,
      decodeTable_canonical hg, decodeTable_canonical hi, decodeTable_canonical hj,
      decodeTable_canonical hk]
  · cases h

/-! ### Source references and events -/

def decodeRef (e : Sx) : Except Error SourceRef :=
  match head e with
  | some (.at, [f, n]) => do pure ⟨← decodeText f, ← decodeText n, none⟩
  | some (.at, [f, n, a, b]) => do
    pure ⟨← decodeText f, ← decodeText n, some (← decodeNat a, ← decodeNat b)⟩
  | _ => bad "expected a source reference"

def encodeRef (r : SourceRef) : Sx :=
  match r.span with
  | none => tagged .at [.atom r.file, .atom r.entry]
  | some (a, b) => tagged .at [.atom r.file, .atom r.entry, encodeNat a, encodeNat b]

theorem decodeRef_canonical {e : Sx} {r : SourceRef} (h : decodeRef e = .ok r) :
    encodeRef r = e := by
  unfold decodeRef at h
  split at h
  · rename_i f n he
    simp only [bind_ok_iff, pure_ok_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeRef, decodeText_canonical ha, decodeText_canonical hb]
  · rename_i f n x y he
    simp only [bind_ok_iff, pure_ok_iff] at h
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeRef, decodeText_canonical ha, decodeText_canonical hb, decodeNat_canonical hc,
      decodeNat_canonical hd]
  · simp at h

section Ids

variable (n : Names)

def decodeInput (e : Sx) : Except Error (DataId × VersionId) :=
  match head e with
  | some (.input, [d, v]) => do pure (⟨← decodeIdx n.data "data" d⟩, ⟨← decodeNat v⟩)
  | _ => bad "expected a run input"

def encodeInput (i : DataId × VersionId) : Sx :=
  tagged .input [encodeIdx n.data i.1.index, encodeNat i.2.index]

theorem decodeInput_canonical {e : Sx} {i : DataId × VersionId} (h : decodeInput n e = .ok i) :
    encodeInput n i = e := by
  unfold decodeInput at h
  split at h
  · rename_i d v he
    simp only [bind_ok_iff, pure_ok_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeInput, decodeIdx_canonical ha, decodeNat_canonical hb]
  · simp at h

def decodeInputs (e : Sx) : Except Error (List (DataId × VersionId)) :=
  match head e with
  | some (.inputs, args) => decodeList (decodeInput n) args
  | _ => bad "expected the run inputs"

def encodeInputs (l : List (DataId × VersionId)) : Sx := tagged .inputs (l.map (encodeInput n))

theorem decodeInputs_canonical {e : Sx} {l : List (DataId × VersionId)}
    (h : decodeInputs n e = .ok l) : encodeInputs n l = e := by
  unfold decodeInputs at h
  split at h
  · rename_i args he
    rw [head_eq_some he, encodeInputs, decodeList_canonical (fun _ _ => decodeInput_canonical n) h]
  · simp at h

def decodeBody (e : Sx) : Except Error Event :=
  match head e with
  | some (.commitPlan, [a, p, v]) => do
    pure (.commitPlan ⟨← decodeIdx n.actor "actor" a⟩ ⟨← decodeIdx n.plan "plan" p⟩
      ⟨← decodeNat v⟩)
  | some (.access, [a, d, pur]) => do
    pure (.access ⟨← decodeIdx n.actor "actor" a⟩ ⟨← decodeIdx n.data "data" d⟩
      (← decodeWord AccessPurpose.spelling "access purpose" pur))
  | some (.run, [r, p, v, ins, f]) => do
    pure (.run ⟨← decodeIdx n.run "run" r⟩ ⟨← decodeIdx n.plan "plan" p⟩ ⟨← decodeNat v⟩
      (← decodeInputs n ins) ⟨← decodeIdx n.family "family" f⟩)
  | some (.result, [r, o]) => do pure (.result ⟨← decodeIdx n.run "run" r⟩ (← decodeNat o))
  | some (.assert, [c, w]) => do
    pure (.assert ⟨← decodeIdx n.claim "claim" c⟩ ⟨← decodeIdx n.witness "witness" w⟩)
  | some (.retract, [src]) => do pure (.retract ⟨← decodeIdx n.source "source" src⟩)
  | some (.updateData, [d, v]) => do
    pure (.updateData ⟨← decodeIdx n.data "data" d⟩ ⟨← decodeNat v⟩)
  | _ => bad "expected an event"

def encodeBody : Event → Sx
  | .commitPlan a p v =>
    tagged .commitPlan [encodeIdx n.actor a.index, encodeIdx n.plan p.index, encodeNat v.index]
  | .access a d pur =>
    tagged .access [encodeIdx n.actor a.index, encodeIdx n.data d.index,
      .atom (AccessPurpose.spelling.text pur)]
  | .run r p v ins f =>
    tagged .run [encodeIdx n.run r.index, encodeIdx n.plan p.index, encodeNat v.index,
      encodeInputs n ins, encodeIdx n.family f.index]
  | .result r o => tagged .result [encodeIdx n.run r.index, encodeNat o]
  | .assert c w => tagged .assert [encodeIdx n.claim c.index, encodeIdx n.witness w.index]
  | .retract src => tagged .retract [encodeIdx n.source src.index]
  | .updateData d v => tagged .updateData [encodeIdx n.data d.index, encodeNat v.index]

theorem decodeBody_canonical {e : Sx} {ev : Event} (h : decodeBody n e = .ok ev) :
    encodeBody n ev = e := by
  unfold decodeBody at h
  split at h <;> (try simp only [bind_ok_iff, pure_ok_iff] at h)
  · rename_i a p v he
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeBody, decodeIdx_canonical hx, decodeIdx_canonical hy, decodeNat_canonical hz]
  · rename_i a d pur he
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeBody, decodeIdx_canonical hx, decodeIdx_canonical hy, decodeWord_canonical hz]
  · rename_i r p v ins f he
    obtain ⟨x, hx, y, hy, z, hz, w, hw, u, hu, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeBody, decodeIdx_canonical hx, decodeIdx_canonical hy, decodeNat_canonical hz,
      decodeInputs_canonical n hw, decodeIdx_canonical hu]
  · rename_i r o he
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeBody, decodeIdx_canonical hx, decodeNat_canonical hy]
  · rename_i c w he
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeBody, decodeIdx_canonical hx, decodeIdx_canonical hy]
  · rename_i src he
    obtain ⟨x, hx, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeBody, decodeIdx_canonical hx]
  · rename_i d v he
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeBody, decodeIdx_canonical hx, decodeNat_canonical hy]
  · simp at h

/-- A universe event: `(event ID BODY)`, with no source reference, since nothing
says it happened. -/
def decodeStamped (e : Sx) : Except Error Stamped :=
  match head e with
  | some (.event, [i, b]) => do pure ⟨⟨← decodeIdx n.event "event" i⟩, ← decodeBody n b⟩
  | _ => bad "expected a universe event"

def encodeStamped (s : Stamped) : Sx :=
  tagged .event [encodeIdx n.event s.id.index, encodeBody n s.event]

theorem decodeStamped_canonical {e : Sx} {s : Stamped} (h : decodeStamped n e = .ok s) :
    encodeStamped n s = e := by
  unfold decodeStamped at h
  split at h
  · rename_i i b he
    simp only [bind_ok_iff, pure_ok_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeStamped, decodeIdx_canonical hx, decodeBody_canonical n hy]
  · simp at h

/-! ### Coverage -/

/-- One optional clause `(TAG ...)` at the front of a clause list. -/
def decodeOpt {α : Type} (t : Tag) (f : List Sx → Except Error α) :
    List Sx → Except Error (Option α × List Sx)
  | [] => .ok (none, [])
  | e :: rest =>
    match head e with
    | some (t', args) => if t' = t then do pure (some (← f args), rest) else .ok (none, e :: rest)
    | none => .ok (none, e :: rest)

def encodeOpt {α : Type} (t : Tag) (g : α → List Sx) : Option α → List Sx
  | none => []
  | some a => [tagged t (g a)]

theorem decodeOpt_canonical {α : Type} {t : Tag} {f : List Sx → Except Error α}
    {g : α → List Sx} (hf : ∀ args a, f args = .ok a → g a = args) {es : List Sx}
    {o : Option α} {rest : List Sx} (h : decodeOpt t f es = .ok (o, rest)) :
    encodeOpt t g o ++ rest = es := by
  unfold decodeOpt at h
  split at h
  · cases h; rfl
  · rename_i e es'
    split at h
    · rename_i t' args he
      split at h
      · subst_vars
        simp only [bind_ok_iff, pure_ok_iff, Prod.mk.injEq] at h
        obtain ⟨a, ha, rfl, rfl⟩ := h
        rw [head_eq_some he]
        simp [encodeOpt, hf args a ha]
      · cases h; rfl
    · cases h; rfl

def decodeKinds (e : Sx) : Except Error (List EventKind) :=
  match head e with
  | some (.kinds, args) => decodeList (decodeWord EventKind.spelling "event kind") args
  | _ => bad "expected the scope kinds"

def encodeKinds (ks : List EventKind) : Sx :=
  tagged .kinds (ks.map fun k => .atom (EventKind.spelling.text k))

theorem decodeKinds_canonical {e : Sx} {ks : List EventKind} (h : decodeKinds e = .ok ks) :
    encodeKinds ks = e := by
  unfold decodeKinds at h
  split at h
  · rename_i args he
    rw [head_eq_some he, encodeKinds, decodeList_canonical (fun _ _ => decodeWord_canonical) h]
  · simp at h

/-- A numeric field `(TAG N)`. -/
def decodeField (t : Tag) (e : Sx) : Except Error Nat :=
  match head e with
  | some (t', [x]) => if t' = t then decodeNat x else bad s!"expected the {t.text} field"
  | _ => bad s!"expected the {t.text} field"

def encodeField (t : Tag) (k : Nat) : Sx := tagged t [encodeNat k]

theorem decodeField_canonical {t : Tag} {e : Sx} {k : Nat} (h : decodeField t e = .ok k) :
    encodeField t k = e := by
  unfold decodeField at h
  split at h
  · rename_i t' x he
    split at h
    · subst_vars; rw [head_eq_some he, encodeField, decodeNat_canonical h]
    · simp at h
  · simp at h

def decodeOneIdx (table : List String) (what : String) : List Sx → Except Error Nat
  | [x] => decodeIdx table what x
  | _ => bad s!"expected one {what} name"

theorem decodeOneIdx_canonical {table : List String} {what : String} {args : List Sx} {i : Nat}
    (h : decodeOneIdx table what args = .ok i) : [encodeIdx table i] = args := by
  unfold decodeOneIdx at h
  split at h
  · rw [decodeIdx_canonical h]
  · simp at h

def decodeScope (e : Sx) : Except Error CoverageScope :=
  match head e with
  | some (.scope, ks :: cut :: rest) => do
    let kinds ← decodeKinds ks
    let cutoff ← decodeField .cutoff cut
    let fam ← decodeOpt .family (decodeOneIdx n.family "family") rest
    let act ← decodeOpt .actors (decodeList (decodeIdx n.actor "actor")) fam.2
    let dat ← decodeOpt .data (decodeList (decodeIdx n.data "data")) act.2
    if dat.2 = [] then
      pure ⟨kinds, fam.1.map FamilyId.mk, act.1.map (List.map ActorId.mk),
        dat.1.map (List.map DataId.mk), cutoff⟩
    else bad "unexpected scope clause"
  | _ => bad "expected a coverage scope"

def encodeScope (sc : CoverageScope) : Sx :=
  tagged .scope ([encodeKinds sc.kinds, encodeField .cutoff sc.cutoff] ++
    encodeOpt .family (fun i => [encodeIdx n.family i]) (sc.family.map FamilyId.index) ++
    encodeOpt .actors (List.map (encodeIdx n.actor)) (sc.actors.map (List.map ActorId.index)) ++
    encodeOpt .data (List.map (encodeIdx n.data)) (sc.data.map (List.map DataId.index)))

theorem decodeScope_canonical {e : Sx} {sc : CoverageScope} (h : decodeScope n e = .ok sc) :
    encodeScope n sc = e := by
  unfold decodeScope at h
  split at h
  · rename_i ks cut rest he
    simp only [bind_ok_iff] at h
    obtain ⟨kinds, hk, cutoff, hc, fam, hf, act, ha, dat, hd, h⟩ := h
    split at h
    · rename_i nil
      simp only [pure_ok_iff] at h
      subst h
      have ef := decodeOpt_canonical (g := fun i => [encodeIdx n.family i])
        (fun _ _ => decodeOneIdx_canonical) (o := fam.1) (rest := fam.2) hf
      have ea := decodeOpt_canonical (g := List.map (encodeIdx n.actor))
        (fun _ _ => decodeList_canonical (fun _ _ => decodeIdx_canonical)) (o := act.1)
        (rest := act.2) ha
      have ed := decodeOpt_canonical (g := List.map (encodeIdx n.data))
        (fun _ _ => decodeList_canonical (fun _ _ => decodeIdx_canonical)) (o := dat.1)
        (rest := dat.2) hd
      rw [nil, List.append_nil] at ed
      rw [head_eq_some he]
      simp only [encodeScope, decodeKinds_canonical hk, decodeField_canonical hc, Option.map_map,
        Function.comp_def, List.map_map, Option.map_id', List.map_id']
      rw [← ef, ← ea, ← ed]
      simp [List.append_assoc]
    · simp at h
  · simp at h

def decodeCoverage (e : Sx) : Except Error (RecordCoverage Empty) :=
  match head e with
  | some (.complete, [sc]) => do pure (.complete (← decodeScope n sc))
  | some (.countBounded, [sc, b]) => do pure (.countBounded (← decodeScope n sc) (← decodeNat b))
  | some (.openWorld, [sc]) => do pure (.openWorld (← decodeScope n sc))
  | some (.declaredPolicy, _) =>
    .error ⟨.unsupported, "process-input 1 interprets no declared reporting policy"⟩
  | _ => bad "expected a coverage assertion"

def encodeCoverage : RecordCoverage Empty → Sx
  | .complete sc => tagged .complete [encodeScope n sc]
  | .countBounded sc b => tagged .countBounded [encodeScope n sc, encodeNat b]
  | .declaredPolicy _ p => p.elim
  | .openWorld sc => tagged .openWorld [encodeScope n sc]

theorem decodeCoverage_canonical {e : Sx} {c : RecordCoverage Empty}
    (h : decodeCoverage n e = .ok c) : encodeCoverage n c = e := by
  unfold decodeCoverage at h
  split at h <;> (try simp only [bind_ok_iff, pure_ok_iff] at h)
  · rename_i sc he
    obtain ⟨x, hx, rfl⟩ := h
    rw [head_eq_some he]; simp [encodeCoverage, decodeScope_canonical n hx]
  · rename_i sc b he
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    rw [head_eq_some he]; simp [encodeCoverage, decodeScope_canonical n hx, decodeNat_canonical hy]
  · rename_i sc he
    obtain ⟨x, hx, rfl⟩ := h
    rw [head_eq_some he]; simp [encodeCoverage, decodeScope_canonical n hx]
  · cases h
  · simp at h

/-! ### Record entries -/

def decodeEntry (e : Sx) : Except Error (AraEntry Empty) :=
  match head e with
  | some (.event, [i, b, r]) => do
    pure (.event ⟨⟨← decodeIdx n.event "event" i⟩, ← decodeBody n b⟩ (← decodeRef r))
  | some (.order, [a, b, r]) => do
    pure (.ordering ⟨← decodeIdx n.event "event" a⟩ ⟨← decodeIdx n.event "event" b⟩
      (← decodeRef r))
  | some (.coverage, [c, r, b]) => do
    pure (.coverage ⟨← decodeCoverage n c, ← decodeRef r,
      ← decodeWord AdmissionBasis.spelling "admission basis" b⟩)
  | some (.submit, [c, w]) => do
    pure (.submission ⟨← decodeIdx n.claim "claim" c⟩ ⟨← decodeIdx n.witness "witness" w⟩)
  | _ => bad "expected a record entry"

def encodeEntry : AraEntry Empty → Sx
  | .event s r => tagged .event [encodeIdx n.event s.id.index, encodeBody n s.event, encodeRef r]
  | .ordering a b r => tagged .order [encodeIdx n.event a.index, encodeIdx n.event b.index, encodeRef r]
  | .coverage c => tagged .coverage [encodeCoverage n c.coverage, encodeRef c.evidence,
      .atom (AdmissionBasis.spelling.text c.basis)]
  | .submission c w => tagged .submit [encodeIdx n.claim c.index, encodeIdx n.witness w.index]

theorem decodeEntry_canonical {e : Sx} {a : AraEntry Empty} (h : decodeEntry n e = .ok a) :
    encodeEntry n a = e := by
  unfold decodeEntry at h
  split at h <;> (try simp only [bind_ok_iff, pure_ok_iff] at h)
  · rename_i i b r he
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeEntry, decodeIdx_canonical hx, decodeBody_canonical n hy, decodeRef_canonical hz]
  · rename_i a b r he
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeEntry, decodeIdx_canonical hx, decodeIdx_canonical hy, decodeRef_canonical hz]
  · rename_i c r b he
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeEntry, decodeCoverage_canonical n hx, decodeRef_canonical hy,
      decodeWord_canonical hz]
  · rename_i c w he
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeEntry, decodeIdx_canonical hx, decodeIdx_canonical hy]
  · simp at h

def decodeRecord (e : Sx) : Except Error (AraSource Empty) :=
  match head e with
  | some (.record, cut :: entries) => do
    let cutoff ← decodeField .cutoff cut
    pure ⟨← decodeList (decodeEntry n) entries, cutoff⟩
  | _ => bad "expected the record"

def encodeRecord (src : AraSource Empty) : Sx :=
  tagged .record (encodeField .cutoff src.cutoff :: src.entries.map (encodeEntry n))

theorem decodeRecord_canonical {e : Sx} {src : AraSource Empty} (h : decodeRecord n e = .ok src) :
    encodeRecord n src = e := by
  unfold decodeRecord at h
  split at h
  · rename_i cut entries he
    simp only [bind_ok_iff, pure_ok_iff] at h
    obtain ⟨c, hc, es, hes, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeRecord, decodeField_canonical hc,
      decodeList_canonical (fun _ _ => decodeEntry_canonical n) hes]
  · simp at h

def decodeUniverse (e : Sx) : Except Error (List Stamped) :=
  match head e with
  | some (.universe, args) => decodeList (decodeStamped n) args
  | _ => bad "expected the universe"

def encodeUniverse (u : List Stamped) : Sx := tagged .universe (u.map (encodeStamped n))

theorem decodeUniverse_canonical {e : Sx} {u : List Stamped} (h : decodeUniverse n e = .ok u) :
    encodeUniverse n u = e := by
  unfold decodeUniverse at h
  split at h
  · rename_i args he
    rw [head_eq_some he, encodeUniverse,
      decodeList_canonical (fun _ _ => decodeStamped_canonical n) h]
  · simp at h

/-! ### Queries -/

def decodeQuery : Sx → Except Error Query
  | .list [.atom t] =>
    if t = Tag.predictable.text then .ok (.atom .predictable) else bad "unknown query form"
  | .list [.atom t, x] =>
    if t = Tag.not.text then do pure (.neg (← decodeQuery x))
    else if t = Tag.runPrecommitted.text then do
      pure (.atom (.runPrecommitted ⟨← decodeIdx n.run "run" x⟩))
    else bad "unknown query form"
  | .list [.atom t, x, y] =>
    if t = Tag.and.text then do pure (.conj (← decodeQuery x) (← decodeQuery y))
    else if t = Tag.or.text then do pure (.disj (← decodeQuery x) (← decodeQuery y))
    else if t = Tag.familyCountAtMost.text then do
      pure (.atom (.familyCountAtMost ⟨← decodeIdx n.family "family" x⟩ (← decodeNat y)))
    else if t = Tag.splitSelection.text then
      match x, y with
      | .list xs, .list ys => do
        pure (.atom (.splitSelection ((← decodeList (decodeIdx n.data "data") xs).map DataId.mk)
          ((← decodeList (decodeIdx n.data "data") ys).map DataId.mk)))
      | _, _ => bad "expected two dataset lists"
    else bad "unknown query form"
  | _ => bad "expected a query formula"

def encodeQuery : Query → Sx
  | .atom .predictable => tagged .predictable []
  | .atom (.runPrecommitted r) => tagged .runPrecommitted [encodeIdx n.run r.index]
  | .atom (.familyCountAtMost f k) => tagged .familyCountAtMost [encodeIdx n.family f.index, encodeNat k]
  | .atom (.splitSelection s t) =>
    tagged .splitSelection [.list (s.map fun d => encodeIdx n.data d.index),
      .list (t.map fun d => encodeIdx n.data d.index)]
  | .neg f => tagged .not [encodeQuery f]
  | .conj f g => tagged .and [encodeQuery f, encodeQuery g]
  | .disj f g => tagged .or [encodeQuery f, encodeQuery g]

theorem decodeQuery_canonical : ∀ {e : Sx} {q : Query}, decodeQuery n e = .ok q → encodeQuery n q = e
  | .list [.atom t], q, h => by
    unfold decodeQuery at h
    split at h
    · cases h; subst_vars; rfl
    · simp at h
  | .list [.atom t, x], q, h => by
    unfold decodeQuery at h
    split at h
    · simp only [bind_ok_iff, pure_ok_iff] at h
      obtain ⟨f, hf, rfl⟩ := h
      subst_vars
      simp [encodeQuery, tagged, decodeQuery_canonical hf]
    · split at h
      · simp only [bind_ok_iff, pure_ok_iff] at h
        obtain ⟨r, hr, rfl⟩ := h
        subst_vars
        simp [encodeQuery, tagged, decodeIdx_canonical hr]
      · simp at h
  | .list [.atom t, x, y], q, h => by
    unfold decodeQuery at h
    split at h
    · simp only [bind_ok_iff, pure_ok_iff] at h
      obtain ⟨f, hf, g, hg, rfl⟩ := h
      subst_vars
      simp [encodeQuery, tagged, decodeQuery_canonical hf, decodeQuery_canonical hg]
    · split at h
      · simp only [bind_ok_iff, pure_ok_iff] at h
        obtain ⟨f, hf, g, hg, rfl⟩ := h
        subst_vars
        simp [encodeQuery, tagged, decodeQuery_canonical hf, decodeQuery_canonical hg]
      · split at h
        · simp only [bind_ok_iff, pure_ok_iff] at h
          obtain ⟨f, hf, k, hk, rfl⟩ := h
          subst_vars
          simp [encodeQuery, tagged, decodeIdx_canonical hf, decodeNat_canonical hk]
        · split at h
          · split at h
            · rename_i xs ys
              simp only [bind_ok_iff, pure_ok_iff] at h
              obtain ⟨as, ha, bs, hb, rfl⟩ := h
              subst_vars
              have ea := decodeList_canonical (fun _ _ => decodeIdx_canonical) ha
              have eb := decodeList_canonical (fun _ _ => decodeIdx_canonical) hb
              simp only [encodeQuery, tagged, List.map_map, Function.comp_def] at ea eb ⊢
              rw [ea, eb]
            · simp at h
          · simp at h
  | .atom _, q, h => by simp [decodeQuery] at h
  | .list [], q, h => by simp [decodeQuery] at h
  | .list (.list _ :: _), q, h => by simp [decodeQuery] at h
  | .list [.atom _, _, _, _], q, h => by simp [decodeQuery] at h
  | .list (.atom _ :: _ :: _ :: _ :: _ :: _), q, h => by simp [decodeQuery] at h

/-- A profile as spelled on the wire. The guarantee level is `num / den` with a
positive denominator. -/
structure ProfileSpec where
  admissible : List EvidenceKind
  accepts : List CoverageKind
  guarantee : GuaranteeClass
  num : Nat
  den : Nat
  probes : List ErrorKind
  acceptance : Acceptance
  deriving DecidableEq, Repr

def ProfileSpec.toProfile (s : ProfileSpec) : Profile Empty where
  admissible := s.admissible.toFinset
  acceptsCoverage c := s.accepts.contains (CoverageKind.of c)
  guarantee := (s.guarantee, (s.num : ℚ) / s.den)
  requiredProbes := s.probes.toFinset
  acceptance := s.acceptance

def decodeWords {α : Type} (t : Tag) (sp : Spelling α) (what : String) (e : Sx) :
    Except Error (List α) :=
  match head e with
  | some (t', args) => if t' = t then decodeList (decodeWord sp what) args
    else bad s!"expected the {t.text} list"
  | none => bad s!"expected the {t.text} list"

def encodeWords {α : Type} (t : Tag) (sp : Spelling α) (l : List α) : Sx :=
  tagged t (l.map fun a => .atom (sp.text a))

theorem decodeWords_canonical {α : Type} {t : Tag} {sp : Spelling α} {what : String} {e : Sx}
    {l : List α} (h : decodeWords t sp what e = .ok l) : encodeWords t sp l = e := by
  unfold decodeWords at h
  split at h
  · rename_i t' args he
    split at h
    · subst_vars
      rw [head_eq_some he, encodeWords, decodeList_canonical (fun _ _ => decodeWord_canonical) h]
    · simp at h
  · simp at h

def decodeGuarantee (e : Sx) : Except Error (GuaranteeClass × Nat × Nat) :=
  match head e with
  | some (.guarantee, [c, a, b]) => do
    let cls ← decodeWord GuaranteeClass.spelling "guarantee class" c
    let num ← decodeNat a
    let den ← decodeNat b
    if 0 < den then pure (cls, num, den) else bad "guarantee level needs a positive denominator"
  | _ => bad "expected the guarantee"

def encodeGuarantee (g : GuaranteeClass × Nat × Nat) : Sx :=
  tagged .guarantee [.atom (GuaranteeClass.spelling.text g.1), encodeNat g.2.1, encodeNat g.2.2]

theorem decodeGuarantee_canonical {e : Sx} {g : GuaranteeClass × Nat × Nat}
    (h : decodeGuarantee e = .ok g) : encodeGuarantee g = e := by
  unfold decodeGuarantee at h
  split at h
  · rename_i c a b he
    simp only [bind_ok_iff] at h
    obtain ⟨cls, hc, num, hn, den, hd, h⟩ := h
    split at h
    · simp only [pure_ok_iff] at h
      subst h
      rw [head_eq_some he, encodeGuarantee, decodeWord_canonical hc, decodeNat_canonical hn,
        decodeNat_canonical hd]
    · simp at h
  · simp at h

def decodeAcceptance (e : Sx) : Except Error Acceptance :=
  match head e with
  | some (.acceptance, [x]) => decodeWord Acceptance.spelling "acceptance" x
  | _ => bad "expected the acceptance"

def encodeAcceptance (a : Acceptance) : Sx := tagged .acceptance [.atom (Acceptance.spelling.text a)]

theorem decodeAcceptance_canonical {e : Sx} {a : Acceptance} (h : decodeAcceptance e = .ok a) :
    encodeAcceptance a = e := by
  unfold decodeAcceptance at h
  split at h
  · rename_i x he
    rw [head_eq_some he, encodeAcceptance, decodeWord_canonical h]
  · simp at h

def decodeProfile (e : Sx) : Except Error ProfileSpec :=
  match head e with
  | some (.profile, [adm, acc, gu, pr, ac]) => do
    let admissible ← decodeWords .admissible EvidenceKind.spelling "evidence kind" adm
    let accepts ← decodeWords .accepts CoverageKind.spelling "coverage kind" acc
    let level ← decodeGuarantee gu
    let probes ← decodeWords .probes ErrorKind.spelling "error kind" pr
    let acceptance ← decodeAcceptance ac
    pure ⟨admissible, accepts, level.1, level.2.1, level.2.2, probes, acceptance⟩
  | _ => bad "expected a profile"

def encodeProfile (s : ProfileSpec) : Sx :=
  tagged .profile [encodeWords .admissible EvidenceKind.spelling s.admissible,
    encodeWords .accepts CoverageKind.spelling s.accepts,
    encodeGuarantee (s.guarantee, s.num, s.den),
    encodeWords .probes ErrorKind.spelling s.probes,
    encodeAcceptance s.acceptance]

theorem decodeProfile_canonical {e : Sx} {s : ProfileSpec} (h : decodeProfile e = .ok s) :
    encodeProfile s = e := by
  unfold decodeProfile at h
  split at h
  · rename_i adm acc gu pr ac he
    simp only [bind_ok_iff, pure_ok_iff] at h
    obtain ⟨a, ha, b, hb, lv, hl, p, hp, x, hx, rfl⟩ := h
    rw [head_eq_some he]
    simp only [encodeProfile, decodeWords_canonical ha, decodeWords_canonical hb,
      decodeGuarantee_canonical hl, decodeWords_canonical hp, decodeAcceptance_canonical hx]
  · simp at h

/-- A query: a verdict on a formula, or an audit of a submitted witness. The
name is a report label at the decode boundary, never interpreted. -/
inductive QuerySpec where
  | verdict (name : String) (q : Query)
  | audit (name : String) (claim : ClaimId) (witness : WitnessId) (profile : ProfileSpec)
  deriving DecidableEq, Repr

def decodeQuerySpec (e : Sx) : Except Error QuerySpec :=
  match head e with
  | some (.verdict, [nm, f]) => do pure (.verdict (← decodeText nm) (← decodeQuery n f))
  | some (.audit, [nm, c, w, p]) => do
    pure (.audit (← decodeText nm) ⟨← decodeIdx n.claim "claim" c⟩
      ⟨← decodeIdx n.witness "witness" w⟩ (← decodeProfile p))
  | _ => bad "expected a query"

def encodeQuerySpec : QuerySpec → Sx
  | .verdict nm q => tagged .verdict [.atom nm, encodeQuery n q]
  | .audit nm c w p =>
    tagged .audit [.atom nm, encodeIdx n.claim c.index, encodeIdx n.witness w.index,
      encodeProfile p]

theorem decodeQuerySpec_canonical {e : Sx} {q : QuerySpec} (h : decodeQuerySpec n e = .ok q) :
    encodeQuerySpec n q = e := by
  unfold decodeQuerySpec at h
  split at h <;> (try simp only [bind_ok_iff, pure_ok_iff] at h)
  · rename_i nm f he
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeQuerySpec, decodeText_canonical ha, decodeQuery_canonical n hb]
  · rename_i nm c w p he
    obtain ⟨a, ha, b, hb, x, hx, y, hy, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeQuerySpec, decodeText_canonical ha, decodeIdx_canonical hb,
      decodeIdx_canonical hx, decodeProfile_canonical hy]
  · simp at h

end Ids

/-! ### Documents -/

/-- Evaluation limits a document declares. The checker's own ceilings
(`maxProcessEvents`, `maxProcessCompletions`) bound them further. -/
structure Limits where
  events : Nat
  completions : Nat
  deriving DecidableEq, Repr

def decodeLimits (e : Sx) : Except Error Limits :=
  match head e with
  | some (.limits, [ev, co]) => do
    pure ⟨← decodeField .events ev, ← decodeField .completions co⟩
  | _ => bad "expected the limits"

def encodeLimits (l : Limits) : Sx :=
  tagged .limits [encodeField .events l.events, encodeField .completions l.completions]

theorem decodeLimits_canonical {e : Sx} {l : Limits} (h : decodeLimits e = .ok l) :
    encodeLimits l = e := by
  unfold decodeLimits at h
  split at h
  · rename_i ev co he
    simp only [bind_ok_iff, pure_ok_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [head_eq_some he]
    simp [encodeLimits, decodeField_canonical ha, decodeField_canonical hb]
  · simp at h

def decodeQueries (n : Names) (e : Sx) : Except Error (List QuerySpec) :=
  match head e with
  | some (.queries, args) => decodeList (decodeQuerySpec n) args
  | _ => bad "expected the queries"

def encodeQueries (n : Names) (qs : List QuerySpec) : Sx := tagged .queries (qs.map (encodeQuerySpec n))

theorem decodeQueries_canonical {n : Names} {e : Sx} {qs : List QuerySpec}
    (h : decodeQueries n e = .ok qs) : encodeQueries n qs = e := by
  unfold decodeQueries at h
  split at h
  · rename_i args he
    rw [head_eq_some he, encodeQueries,
      decodeList_canonical (fun _ _ => decodeQuerySpec_canonical n) h]
  · simp at h

/-- A decoded `process-input 1` document. -/
structure Document where
  names : Names
  source : AraSource Empty
  admits : List AdmissionBasis
  unrecorded : List Stamped
  limits : Limits
  queries : List QuerySpec
  deriving DecidableEq, Repr

/-- Version 1 is exact: other spellings, including `01`, are not aliases. -/
def version : String := "1"

def decodeDocument (e : Sx) : Except Error Document :=
  match head e with
  | some (.processInput, .atom v :: rest) =>
    if v = version then
      match rest with
      | [ns, rec, rd, un, lim, qs] => do
        let n ← decodeNames ns
        let source ← decodeRecord n rec
        let admits ← decodeWords .reader AdmissionBasis.spelling "admission basis" rd
        let unrecorded ← decodeUniverse n un
        let limits ← decodeLimits lim
        let queries ← decodeQueries n qs
        pure ⟨n, source, admits, unrecorded, limits, queries⟩
      | _ => bad "expected names, record, reader, universe, limits and queries"
    else .error ⟨.unsupportedVersion, "process-input supports version 1 only"⟩
  | some (.processInput, _) => .error ⟨.unsupportedVersion, "process-input supports version 1 only"⟩
  | _ => bad "expected a process-input document"

def encodeDocument (d : Document) : Sx :=
  tagged .processInput [.atom version, encodeNames d.names, encodeRecord d.names d.source,
    encodeWords .reader AdmissionBasis.spelling d.admits, encodeUniverse d.names d.unrecorded,
    encodeLimits d.limits, encodeQueries d.names d.queries]

/-- The decoder loses nothing: every accepted document re-encodes to the exact
S-expression it came from. -/
theorem decodeDocument_canonical {e : Sx} {d : Document} (h : decodeDocument e = .ok d) :
    encodeDocument d = e := by
  unfold decodeDocument at h
  split at h
  · rename_i v rest he
    split at h
    · rename_i hv
      split at h
      · rename_i ns rec rd un lim qs
        simp only [bind_ok_iff, pure_ok_iff] at h
        obtain ⟨n, hn, src, hs, ad, ha, u, hu, l, hl, q, hq, rfl⟩ := h
        rw [head_eq_some he, hv]
        simp only [encodeDocument, decodeNames_canonical hn, decodeRecord_canonical n hs,
          decodeWords_canonical ha, decodeUniverse_canonical n hu, decodeLimits_canonical hl,
          decodeQueries_canonical hq]
      · simp at h
    · cases h
  · cases h
  · simp at h

/-- Every decodable document survives an encode/decode round trip. -/
theorem decode_encode {e : Sx} {d : Document} (h : decodeDocument e = .ok d) :
    decodeDocument (encodeDocument d) = .ok d := by
  rw [decodeDocument_canonical h, h]

end Lara.Process.Wire
