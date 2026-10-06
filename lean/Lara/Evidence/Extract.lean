import Lara.Evidence.Types

namespace Lara.Evidence
open Lara

private def digit (c : Char) : Bool := decide ('0' ≤ c ∧ c ≤ '9')
private def digits (cs : List Char) : Bool := !cs.isEmpty && cs.all digit
private def signed (cs : List Char) : Bool × List Char :=
  match cs with
  | '-' :: rest => (true, rest)
  | '+' :: rest => (false, rest)
  | rest => (false, rest)

/-- Exact bounded scientific decimal decoding. No binary floating point enters
this function. Bounds are checked before conversion, padding or exponentiation. -/
def decimal? (s : String) : Option String := do
  let (negative, body) := signed s.toList
  let (mantissa, exponentPart) := body.span (fun c => c != 'e' && c != 'E')
  let exponent ← match exponentPart with
    | [] => some (0 : Int)
    | _ :: rest => do
        let (neg, ds) := signed rest
        if !digits ds || ds.length > 3 then none else do
          let n ← (String.ofList ds).toNat?
          if n > 256 then none else some (if neg then -(Int.ofNat n) else Int.ofNat n)
  let (whole, fractionPart) := mantissa.span (fun c => c != '.')
  let fraction ← match fractionPart with
    | [] => some []
    | '.' :: rest => if digits rest then some rest else none
    | _ => none
  if !digits whole || whole.length + fraction.length > 256 then none else
    let ds := whole ++ fraction
    let point := Int.ofNat whole.length + exponent
    let expanded :=
      if point ≤ 0 then "0." ++ String.ofList (List.replicate (-point).toNat '0' ++ ds)
      else if point ≥ Int.ofNat ds.length then
        String.ofList (ds ++ List.replicate (point.toNat - ds.length) '0')
      else String.ofList (ds.take point.toNat) ++ "." ++ String.ofList (ds.drop point.toNat)
    some (canonNum ((if negative then "-" else "") ++ expanded))

def decimalLine? (s : String) : Option String :=
  match s.toList.reverse with
  | '\n' :: rest => decimal? (String.ofList rest.reverse)
  | _ => none

inductive Scalar where
  | csv : String → Scalar
  | jsonString : String → Scalar
  | jsonNumber : String → Scalar
  | other : Scalar
  deriving DecidableEq

def decodeScalar : TermEncoding → Scalar → Option Term
  | .text, .csv s | .text, .jsonString s => some (.str s)
  | .decimal, .csv s | .decimal, .jsonNumber s => (decimal? s).map .num
  | .decimalLine, .jsonString s => (decimalLine? s).map .num
  | _, _ => none

/-- Independent scalar typing relation: decimal-line is only a JSON string,
text never coerces numbers, and decimal never coerces JSON strings. -/
inductive ScalarDecodes : TermEncoding → Scalar → Term → Prop where
  | csvText : ScalarDecodes .text (.csv s) (.str s)
  | jsonText : ScalarDecodes .text (.jsonString s) (.str s)
  | csvDecimal : decimal? s = some n → ScalarDecodes .decimal (.csv s) (.num n)
  | jsonDecimal : decimal? s = some n → ScalarDecodes .decimal (.jsonNumber s) (.num n)
  | jsonDecimalLine : decimalLine? s = some n → ScalarDecodes .decimalLine (.jsonString s) (.num n)

theorem decodeScalar_iff {e s t} : decodeScalar e s = some t ↔ ScalarDecodes e s t := by
  constructor
  · intro h
    cases e with
    | text =>
      cases s with
      | csv raw => simp [decodeScalar] at h; subst t; exact .csvText
      | jsonString raw => simp [decodeScalar] at h; subst t; exact .jsonText
      | jsonNumber raw => simp [decodeScalar] at h
      | other => simp [decodeScalar] at h
    | decimal =>
      cases s with
      | csv raw =>
        cases hd : decimal? raw with
        | none => simp [decodeScalar, hd] at h
        | some n => simp [decodeScalar, hd] at h; subst t; exact .csvDecimal hd
      | jsonNumber raw =>
        cases hd : decimal? raw with
        | none => simp [decodeScalar, hd] at h
        | some n => simp [decodeScalar, hd] at h; subst t; exact .jsonDecimal hd
      | jsonString raw => simp [decodeScalar] at h
      | other => simp [decodeScalar] at h
    | decimalLine =>
      cases s with
      | jsonString raw =>
        cases hd : decimalLine? raw with
        | none => simp [decodeScalar, hd] at h
        | some n => simp [decodeScalar, hd] at h; subst t; exact .jsonDecimalLine hd
      | csv raw => simp [decodeScalar] at h
      | jsonNumber raw => simp [decodeScalar] at h
      | other => simp [decodeScalar] at h
  · intro h; cases h <;> simp_all [decodeScalar]

def column? (header : List ColumnName) (row : List String) (c : ColumnName) : Option String :=
  match header, row with
  | h :: hs, v :: vs => if h = c then some v else column? hs vs c
  | _, _ => none

inductive ColumnSelected : List ColumnName → List String → ColumnName → String → Prop where
  | head : ColumnSelected (c :: hs) (v :: vs) c v
  | tail : h ≠ c → ColumnSelected hs vs c v → ColumnSelected (h :: hs) (x :: vs) c v

theorem column_iff {hs row c v} : column? hs row c = some v ↔ ColumnSelected hs row c v := by
  induction hs generalizing row with
  | nil => cases row <;> simp [column?] <;> intro h <;> cases h
  | cons h hs ih =>
      cases row with
      | nil => simp [column?]; intro h; cases h
      | cons x xs =>
          by_cases hc : h = c
          · subst h; simp [column?]
            constructor
            · intro hx; subst x; exact .head
            · intro hx; cases hx with
              | head => rfl
              | tail hn _ => exact False.elim (hn rfl)
          · simp [column?, hc]
            constructor
            · intro hsel; exact .tail hc (ih.mp hsel)
            · intro hsel; cases hsel with
              | head => exact False.elim (hc rfl)
              | tail _ ht => exact ih.mpr ht

def csvRows (t : CsvTable) (key : ColumnName) (value : String) : List (List String) :=
  t.rows.filter (fun row => column? t.header row key == some value)
def csvWellFormed (t : CsvTable) : Bool :=
  decide (t.header.Nodup ∧ t.header.length ≤ 256 ∧ t.rows.length ≤ 100000) &&
    t.rows.all (fun row => row.length == t.header.length)
def csvSelect (t : CsvTable) (key : ColumnName) (value : String)
    (selectors : List CsvSelector) : Option (List Term) := do
  if !csvWellFormed t then none else do
    let row ← match csvRows t key value with | [r] => some r | _ => none
    selectors.mapM fun sel => do
      let raw ← column? t.header row sel.column
      decodeScalar sel.encoding (.csv raw)

/-- Unique-row selection requires the entire typed table to be well formed,
not merely the selected prefix. -/
def CsvUniqueRow (t : CsvTable) (key : ColumnName) (value : String) (row : List String) : Prop :=
  (t.header.Nodup ∧ t.header.length ≤ 256 ∧ t.rows.length ≤ 100000) ∧
    (∀ r ∈ t.rows, r.length = t.header.length) ∧
    csvRows t key value = [row]

inductive CsvColumns (header : List ColumnName) (row : List String) :
    List CsvSelector → List Term → Prop where
  | nil : CsvColumns header row [] []
  | cons : ColumnSelected header row sel.column raw →
      ScalarDecodes sel.encoding (.csv raw) term → CsvColumns header row sels terms →
      CsvColumns header row (sel :: sels) (term :: terms)

theorem csvColumns_iff {header row sels terms} :
    sels.mapM (fun sel => do
      let raw ← column? header row sel.column
      decodeScalar sel.encoding (.csv raw)) = some terms ↔
      CsvColumns header row sels terms := by
  induction sels generalizing terms with
  | nil => simp; constructor
           · intro h; subst terms; constructor
           · intro h; cases h; rfl
  | cons sel sels ih =>
      constructor
      · intro h
        cases hc : column? header row sel.column with
        | none => simp [hc] at h
        | some raw =>
          cases hd : decodeScalar sel.encoding (.csv raw) with
          | none => simp [hc, hd] at h
          | some term =>
            cases ht : sels.mapM (fun sel => do
                let raw ← column? header row sel.column
                decodeScalar sel.encoding (.csv raw)) with
            | none =>
              simp only [List.mapM_cons, hc, ht] at h
              simp [hd] at h
            | some ts =>
              simp only [List.mapM_cons, hc, ht] at h
              simp [hd] at h
              subst terms
              exact .cons (column_iff.mp hc) (decodeScalar_iff.mp hd) (ih.mp ht)
      · intro h; cases h with
        | cons hc hd ht =>
          simp only [List.mapM_cons, column_iff.mpr hc, ih.mpr ht]
          simp [decodeScalar_iff.mpr hd]

def jsonEntry? : JsonEntries → JsonToken → Option JsonValue
  | .nil, _ => none
  | .cons k v rest, token => if k = token then some v else jsonEntry? rest token
def jsonIndex? : JsonValues → Nat → Option JsonValue
  | .nil, _ => none
  | .cons v _, 0 => some v
  | .cons _ rest, n + 1 => jsonIndex? rest n
def arrayIndex? (token : JsonToken) : Option Nat := do
  let n ← token.val.toNat?
  if toString n = token.val then some n else none

def pointer? : JsonValue → JsonPath → Option JsonValue
  | v, [] => some v
  | .object entries, token :: rest => do
      let v ← jsonEntry? entries token
      pointer? v rest
  | .array values, token :: rest => do
      let index ← arrayIndex? token
      let v ← jsonIndex? values index
      pointer? v rest
  | _, _ => none

inductive PointerResolves : JsonValue → JsonPath → JsonValue → Prop where
  | root : PointerResolves v [] v
  | object : jsonEntry? entries token = some v → PointerResolves v rest out →
      PointerResolves (.object entries) (token :: rest) out
  | array : arrayIndex? token = some n → jsonIndex? values n = some v →
      PointerResolves v rest out → PointerResolves (.array values) (token :: rest) out

theorem pointer_iff {value path out} : pointer? value path = some out ↔ PointerResolves value path out := by
  induction path generalizing value with
  | nil => simp [pointer?]; constructor
           · intro h; subst value; constructor
           · intro h; cases h; rfl
  | cons token rest ih =>
      constructor
      · intro h
        cases value with
        | object entries =>
          cases he : jsonEntry? entries token with
          | none => simp [pointer?, he] at h
          | some v =>
            exact .object he (ih.mp (by simpa [pointer?, he] using h))
        | array values =>
          cases hi : arrayIndex? token with
          | none => simp [pointer?, hi] at h
          | some n =>
            cases he : jsonIndex? values n with
            | none => simp [pointer?, hi, he] at h
            | some v =>
              exact .array hi he (ih.mp (by simpa [pointer?, hi, he] using h))
        | string s => simp [pointer?] at h
        | number n => simp [pointer?] at h
        | bool b => simp [pointer?] at h
        | null => simp [pointer?] at h
      · intro h; cases h with
        | object he hp => simp [pointer?, he, ih.mpr hp]
        | array hi he hp => simp [pointer?, hi, he, ih.mpr hp]

theorem pointer_unique (h₁ : PointerResolves value path a) (h₂ : PointerResolves value path b) : a = b := by
  have := (pointer_iff.mpr h₁).symm.trans (pointer_iff.mpr h₂)
  exact Option.some.inj this

def jsonScalar : JsonValue → Scalar
  | .string s => .jsonString s
  | .number n => .jsonNumber n
  | _ => .other

def jsonSelect (value : JsonValue) (selectors : List JsonSelector) : Option (List Term) :=
  selectors.mapM fun sel => do
    let v ← pointer? value sel.path
    decodeScalar sel.encoding (jsonScalar v)

inductive JsonColumns (value : JsonValue) : List JsonSelector → List Term → Prop where
  | nil : JsonColumns value [] []
  | cons : PointerResolves value sel.path scalar →
      ScalarDecodes sel.encoding (jsonScalar scalar) term → JsonColumns value sels terms →
      JsonColumns value (sel :: sels) (term :: terms)

theorem jsonColumns_iff {value sels terms} :
    jsonSelect value sels = some terms ↔ JsonColumns value sels terms := by
  induction sels generalizing terms with
  | nil => simp [jsonSelect]; constructor
           · intro h; subst terms; constructor
           · intro h; cases h; rfl
  | cons sel sels ih =>
      constructor
      · intro h
        cases hp : pointer? value sel.path with
        | none => simp [jsonSelect, hp] at h
        | some scalar =>
          cases hd : decodeScalar sel.encoding (jsonScalar scalar) with
          | none => simp [jsonSelect, hp, hd] at h
          | some term =>
            cases ht : jsonSelect value sels with
            | none =>
              simp only [jsonSelect] at ht
              simp only [jsonSelect, List.mapM_cons, hp, ht] at h
              simp [hd] at h
            | some ts =>
              have ht' := ht
              simp only [jsonSelect] at ht'
              simp only [jsonSelect, List.mapM_cons, hp, ht'] at h
              simp [hd] at h
              subst terms
              exact .cons (pointer_iff.mp hp) (decodeScalar_iff.mp hd) (ih.mp ht)
      · intro h; cases h with
        | cons hp hd ht =>
          have htail := ih.mpr ht
          simp only [jsonSelect] at htail
          simp only [jsonSelect, List.mapM_cons, pointer_iff.mpr hp, htail]
          simp [decodeScalar_iff.mpr hd]

def jsonKeys : JsonEntries → List JsonToken
  | .nil => []
  | .cons key _ rest => key :: jsonKeys rest
mutual
  def jsonWellFormed : JsonValue → Bool
    | .object entries => jsonEntriesWellFormed entries
    | .array values => jsonValuesWellFormed values
    | _ => true
  def jsonEntriesWellFormed : JsonEntries → Bool
    | .nil => true
    | .cons key value rest =>
      !(decide (key ∈ jsonKeys rest)) && jsonWellFormed value && jsonEntriesWellFormed rest
  def jsonValuesWellFormed : JsonValues → Bool
    | .nil => true
    | .cons value rest => jsonWellFormed value && jsonValuesWellFormed rest
end

mutual
  def jsonMeasure : JsonValue → Nat × Nat
    | .object entries =>
      let m := jsonEntriesMeasure entries
      (m.1 + 1, m.2 + 1)
    | .array values =>
      let m := jsonValuesMeasure values
      (m.1 + 1, m.2 + 1)
    | _ => (1, 0)
  def jsonEntriesMeasure : JsonEntries → Nat × Nat
    | .nil => (0, 0)
    | .cons _ value rest =>
      let a := jsonMeasure value
      let b := jsonEntriesMeasure rest
      (a.1 + b.1, max a.2 b.2)
  def jsonValuesMeasure : JsonValues → Nat × Nat
    | .nil => (0, 0)
    | .cons value rest =>
      let a := jsonMeasure value
      let b := jsonValuesMeasure rest
      (a.1 + b.1, max a.2 b.2)
end
def jsonWithinBounds (value : JsonValue) : Bool :=
  let m := jsonMeasure value
  decide (m.1 ≤ 100000 ∧ m.2 ≤ 128)

def termsOfList : List Term → Terms
  | [] => .nil
  | t :: ts => .cons t (termsOfList ts)
def extract (r : ExtractionRequest) (objects : List CapturedObject) : Except String Atom :=
  match r, objects with
  | .csvRowRequest _ _ key value sels pred, [⟨_, .csv table⟩] =>
      match csvSelect table key value sels with
      | some terms => .ok (.atom pred (termsOfList terms))
      | none => .error "csv-selection"
  | .jsonPointerRequest _ _ sels pred, [⟨_, .json value⟩] =>
      if !jsonWellFormed value || !jsonWithinBounds value then .error "json-selection" else
        match jsonSelect value sels with
        | some terms => .ok (.atom pred (termsOfList terms))
        | none => .error "json-selection"
  | _, _ => .error "payload-type"

theorem csv_unique_row {t key value a b}
    (ha : CsvUniqueRow t key value a) (hb : CsvUniqueRow t key value b) : a = b := by
  have h := ha.2.2.symm.trans hb.2.2
  simpa using h

theorem csvWellFormed_iff {table : CsvTable} : csvWellFormed table = true ↔
    (table.header.Nodup ∧ table.header.length ≤ 256 ∧ table.rows.length ≤ 100000) ∧
      ∀ row ∈ table.rows, row.length = table.header.length := by
  simp [csvWellFormed, List.all_eq_true]

theorem csvSelect_iff {table key value selectors terms} :
    csvSelect table key value selectors = some terms ↔
      ∃ row, CsvUniqueRow table key value row ∧
        CsvColumns table.header row selectors terms := by
  constructor
  · intro h
    cases hw : csvWellFormed table with
    | false => simp [csvSelect, hw] at h
    | true =>
      have hwell := csvWellFormed_iff.mp hw
      cases hr : csvRows table key value with
      | nil => simp [csvSelect, hw, hr] at h
      | cons row rest =>
        cases rest with
        | nil =>
          exact ⟨row, ⟨hwell.1, hwell.2, hr⟩,
            csvColumns_iff.mp (by simpa [csvSelect, hw, hr] using h)⟩
        | cons second rest => simp [csvSelect, hw, hr] at h
  · rintro ⟨row, ⟨hheader, hwidth, hrow⟩, hcols⟩
    have hw := csvWellFormed_iff.mpr ⟨hheader, hwidth⟩
    simpa [csvSelect, hw, hrow] using csvColumns_iff.mpr hcols

theorem extract_csv_exact {version object key value selectors predicate metadata table row terms}
    (hrow : CsvUniqueRow table key value row)
    (hcols : CsvColumns table.header row selectors terms) :
    extract (.csvRowRequest version object key value selectors predicate) [⟨metadata, .csv table⟩] =
      .ok (.atom predicate (termsOfList terms)) := by
  simp [extract, csvSelect_iff.mpr ⟨row, hrow, hcols⟩]

theorem extract_json_exact {version object selectors predicate metadata value terms}
    (hwell : jsonWellFormed value = true)
    (hbound : jsonWithinBounds value = true)
    (hcols : JsonColumns value selectors terms) :
    extract (.jsonPointerRequest version object selectors predicate) [⟨metadata, .json value⟩] =
      .ok (.atom predicate (termsOfList terms)) := by
  simp [extract, hwell, hbound, jsonColumns_iff.mpr hcols]

theorem extracted_normal_form
    {output declared : Atom} (h : nf canonNum output = nf canonNum declared) :
    equiv canonNum output declared := h

/-- These specifications operate on typed tables/trees and exact scalar lexemes.
Concrete UTF8/CSV/JSON parsing, duplicate-key rejection before tree construction,
OS descriptor capture, hashes and compiler/runtime remain refinement premises. -/
def TypedParserRefinement (decode : String → Option Payload)
    (bytes : String) (typed : Payload) : Prop := decode bytes = some typed

end Lara.Evidence
