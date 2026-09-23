/-
Versioned outer-surface S-expression codec.

Structured decoding is total and its round trips are proved below. Text reading
and printing reuse Lara.Driver's existing executable boundary; their byte-level
correctness is tested, not included in the structured round-trip theorem.
Decoding preserves declaration order and duplicates. Environment loading owns
name uniqueness and semantic obligations; a wire clause is never evidence.
-/
import Lara.PW.Surface
import Lara.Driver

namespace Lara.PW.Wire
open Lara.PW.Surface
open Lara.Grounded (Status)
open Lara.Driver (Sx)

/-- Closed outer grammar vocabulary. Clause spellings belong to Surface.Clause.
`num`, `str`, `con` and `atom` encode the same `Term`/`Atom` shape as the inner
wire, so their spellings come from `Lara.Driver.tagToString`; the symbol entry
`(con SOURCE TARGET)` reuses the constructor spelling. Tags that merely share an
inner spelling (`pred`, `leaf`, `queries`, ...) head different forms and keep
their own entries. -/
inductive Tag where
  | document | bridges | queries | bridge | symbols | leaves | clauses | pred | con | leaf | pose | status | top | neg | conj | box | dia | atom | num | str
deriving DecidableEq, Repr

def Tag.text : Tag → String
  | .document => "pw-surface"
  | .bridges => "bridges"
  | .queries => "queries"
  | .bridge => "bridge"
  | .symbols => "symbols"
  | .leaves => "leaves"
  | .clauses => "clauses"
  | .pred => "pred"
  | .con => Lara.Driver.tagToString .conApp
  | .leaf => "leaf"
  | .pose => "pose"
  | .status => "status"
  | .top => "top"
  | .neg => "not"
  | .conj => "and"
  | .box => "box"
  | .dia => "dia"
  | .atom => Lara.Driver.tagToString .atom
  | .num => Lara.Driver.tagToString .numLit
  | .str => Lara.Driver.tagToString .strLit

/-- Parse a keyword using its single spelling table. -/
def Tag.parse (s : String) : Option Tag :=
  if s = Tag.text .document then some .document else
  if s = Tag.text .bridges then some .bridges else
  if s = Tag.text .queries then some .queries else
  if s = Tag.text .bridge then some .bridge else
  if s = Tag.text .symbols then some .symbols else
  if s = Tag.text .leaves then some .leaves else
  if s = Tag.text .clauses then some .clauses else
  if s = Tag.text .pred then some .pred else
  if s = Tag.text .con then some .con else
  if s = Tag.text .leaf then some .leaf else
  if s = Tag.text .pose then some .pose else
  if s = Tag.text .status then some .status else
  if s = Tag.text .top then some .top else
  if s = Tag.text .neg then some .neg else
  if s = Tag.text .conj then some .conj else
  if s = Tag.text .box then some .box else
  if s = Tag.text .dia then some .dia else
  if s = Tag.text .atom then some .atom else
  if s = Tag.text .num then some .num else
  if s = Tag.text .str then some .str else
  none

@[simp] theorem Tag.parse_text (t : Tag) : Tag.parse t.text = some t := by
  cases t <;> decide

/-- The concrete vocabulary has no aliases or spelling collisions. -/
theorem Tag.text_injective : Function.Injective Tag.text := by
  intro a b h
  have hp := congrArg Tag.parse h
  simpa using hp

/-- Stable categories; detail strings describe boundary data, never drive logic. -/
inductive ErrorTag where
  | syntax | malformed | unsupportedVersion
  deriving DecidableEq, Repr

def ErrorTag.text : ErrorTag → String
  | .syntax => "syntax"
  | .malformed => "malformed"
  | .unsupportedVersion => "unsupported-version"

structure Error where
  tag : ErrorTag
  detail : String
  deriving DecidableEq, Repr

private def malformed (what : String) : Except Error α :=
  .error ⟨.malformed, what⟩

/-- The versioned unit of outer authoring; all lists retain authored order. -/
structure Document where
  bridges : List BridgeDecl
  queries : List Posed
  deriving DecidableEq

/-- Version 1 is exact: other spellings (including 01) are not aliases. -/
def version : String := "1"

def tagged (t : Tag) (args : List Sx) : Sx := .list (.atom t.text :: args)

/-- Read a tagged form. Arity checking belongs to its constructor decoder. -/
def head (e : Sx) : Option (Tag × List Sx) :=
  match e with
  | .list (.atom s :: args) => (Tag.parse s).map (·, args)
  | _ => none

@[simp] theorem head_tagged (t : Tag) (args : List Sx) :
    head (tagged t args) = some (t, args) := by
  simp [head, tagged]

@[simp] theorem bind_ok {α β : Type u} (a : α) (f : α → Except Error β) :
    (Except.ok a >>= f) = f a := rfl

@[simp] theorem map_ok {α β : Type u} (a : α) (f : α → β) :
    (f <$> (Except.ok a : Except Error α)) = .ok (f a) := rfl

/-- Total sequence decoder, preserving order and the first failure. -/
def decodeList (f : Sx → Except Error α) : List Sx → Except Error (List α)
  | [] => .ok []
  | x :: xs => do
    let a ← f x
    let rest ← decodeList f xs
    pure (a :: rest)

@[simp] theorem decodeList_map (f : Sx → Except Error α) (g : α → Sx)
    (h : ∀ a, f (g a) = .ok a) (xs : List α) :
    decodeList f (xs.map g) = .ok xs := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [decodeList, h, ih]

mutual
  def encodeTerm : Term → Sx
    | .num s => tagged .num [.atom s]
    | .str s => tagged .str [.atom s]
    | .con k ts => tagged .con (.atom k :: encodeTerms ts)
  def encodeTerms : Terms → List Sx
    | .nil => []
    | .cons t ts => encodeTerm t :: encodeTerms ts
end

-- Match the token tree directly so recursive size decrease is visible to Lean.
mutual
  def decodeTerm (e : Sx) : Except Error Term :=
    match e with
    | .list (.atom tag :: args) =>
      match Tag.parse tag, args with
      | some .num, [.atom s] => .ok (.num s)
      | some .str, [.atom s] => .ok (.str s)
      | some .con, .atom k :: ts => do
        let terms ← decodeTerms ts
        pure (.con k terms)
      | _, _ => malformed "term"
    | _ => malformed "term"
  termination_by sizeOf e
  def decodeTerms (es : List Sx) : Except Error Terms :=
    match es with
    | [] => .ok .nil
    | t :: ts => do
      let term ← decodeTerm t
      let terms ← decodeTerms ts
      pure (.cons term terms)
  termination_by sizeOf es
end

mutual
  @[simp] theorem decodeTerm_encode (t : Term) :
      decodeTerm (encodeTerm t) = .ok t := by
    cases t with
    | num s => simp [encodeTerm, tagged, decodeTerm]
    | str s => simp [encodeTerm, tagged, decodeTerm]
    | con k ts => simp [encodeTerm, tagged, decodeTerm, decodeTerms_encode ts]
  @[simp] theorem decodeTerms_encode (ts : Terms) :
      decodeTerms (encodeTerms ts) = .ok ts := by
    cases ts with
    | nil => simp [encodeTerms, decodeTerms]
    | cons t ts => simp [encodeTerms, decodeTerms, decodeTerm_encode t, decodeTerms_encode ts]
end

def encodeAtom : Atom → Sx
  | .atom p ts => tagged .atom (.atom p :: encodeTerms ts)

def decodeAtom (e : Sx) : Except Error Atom :=
  match head e with
  | some (.atom, .atom p :: ts) => do
    let terms ← decodeTerms ts
    pure (.atom p terms)
  | _ => malformed "atom"

@[simp] theorem decodeAtom_encode (a : Atom) : decodeAtom (encodeAtom a) = .ok a := by
  cases a with
  | atom p ts => simp [encodeAtom, decodeAtom]

/-- Status spellings use the existing inner wire vocabulary. -/
def statusTag : Status → Lara.Driver.Tag
  | .justified => .justified
  | .contested => .contested
  | .defeated => .defeated
  | .gap => .gap

def encodeStatus (s : Status) : Sx := .atom (Lara.Driver.tagToString (statusTag s))

def decodeStatus : Sx → Except Error Status
  | .atom s =>
    if s = Lara.Driver.tagToString (statusTag .justified) then .ok .justified else
    if s = Lara.Driver.tagToString (statusTag .contested) then .ok .contested else
    if s = Lara.Driver.tagToString (statusTag .defeated) then .ok .defeated else
    if s = Lara.Driver.tagToString (statusTag .gap) then .ok .gap else
    malformed "status"
  | _ => malformed "status"

@[simp] theorem decodeStatus_encode (s : Status) :
    decodeStatus (encodeStatus s) = .ok s := by
  cases s <;> rfl

def encodeClause (c : Clause) : Sx := .atom c.text

def decodeClause : Sx → Except Error Clause
  | .atom s =>
    if s = Clause.text .leafOk then .ok .leafOk else
    if s = Clause.text .ruleOk then .ok .ruleOk else
    if s = Clause.text .certOk then .ok .certOk else
    malformed "clause"
  | _ => malformed "clause"

@[simp] theorem decodeClause_encode (c : Clause) :
    decodeClause (encodeClause c) = .ok c := by
  cases c <;> rfl

def encodeSymEntry : SymEntry → Sx
  | .pred s t => tagged .pred [.atom s.name, .atom t.name]
  | .con s t => tagged .con [.atom s.name, .atom t.name]

def decodeSymEntry (e : Sx) : Except Error SymEntry :=
  match head e with
  | some (.pred, [.atom s, .atom t]) => .ok (.pred ⟨s⟩ ⟨t⟩)
  | some (.con, [.atom s, .atom t]) => .ok (.con ⟨s⟩ ⟨t⟩)
  | _ => malformed "symbol-entry"

@[simp] theorem decodeSymEntry_encode (e : SymEntry) :
    decodeSymEntry (encodeSymEntry e) = .ok e := by
  cases e <;> simp [encodeSymEntry, decodeSymEntry]

def encodeLeafEntry (e : LeafEntry) : Sx :=
  tagged .leaf [.atom e.source.name, .atom e.target.name]

def decodeLeafEntry (e : Sx) : Except Error LeafEntry :=
  match head e with
  | some (.leaf, [.atom s, .atom t]) => .ok ⟨⟨s⟩, ⟨t⟩⟩
  | _ => malformed "leaf-entry"

@[simp] theorem decodeLeafEntry_encode (e : LeafEntry) :
    decodeLeafEntry (encodeLeafEntry e) = .ok e := by
  simp [encodeLeafEntry, decodeLeafEntry]

def encodeBridgeDecl (d : BridgeDecl) : Sx :=
  tagged .bridge [.atom d.id.name, .atom d.source.name, .atom d.target.name,
    tagged .symbols (d.symbols.map encodeSymEntry),
    tagged .leaves (d.leaves.map encodeLeafEntry),
    tagged .clauses (d.clauses.map encodeClause)]

/-- Decode exactly one named section. Extra/missing fields cannot be ignored. -/
def sectionItems (t : Tag) (e : Sx) : Except Error (List Sx) :=
  match head e with
  | some (found, xs) => if found = t then .ok xs else malformed t.text
  | _ => malformed t.text

@[simp] theorem sectionItems_tagged (t : Tag) (xs : List Sx) :
    sectionItems t (tagged t xs) = .ok xs := by
  simp [sectionItems]

def decodeBridgeDecl (e : Sx) : Except Error BridgeDecl :=
  match head e with
  | some (.bridge, [.atom id, .atom src, .atom dst, syms, leaves, clauses]) => do
    let symbols ← decodeList decodeSymEntry (← sectionItems .symbols syms)
    let leaves ← decodeList decodeLeafEntry (← sectionItems .leaves leaves)
    let clauses ← decodeList decodeClause (← sectionItems .clauses clauses)
    pure ⟨⟨id⟩, ⟨src⟩, ⟨dst⟩, symbols, leaves, clauses⟩
  | _ => malformed "bridge"

@[simp] theorem decodeBridgeDecl_encode (d : BridgeDecl) :
    decodeBridgeDecl (encodeBridgeDecl d) = .ok d := by
  simp [encodeBridgeDecl, decodeBridgeDecl]

def encodeForm : SForm → Sx
  | .status s a => tagged .status [encodeStatus s, encodeAtom a]
  | .top => tagged .top []
  | .neg f => tagged .neg [encodeForm f]
  | .conj f g => tagged .conj [encodeForm f, encodeForm g]
  | .box b f => tagged .box [.atom b.name, encodeForm f]
  | .dia b f => tagged .dia [.atom b.name, encodeForm f]

def decodeForm (e : Sx) : Except Error SForm :=
  match e with
  | .list (.atom tag :: args) =>
    match Tag.parse tag, args with
    | some .status, [s, a] => do
      let status ← decodeStatus s
      let atom ← decodeAtom a
      pure (.status status atom)
    | some .top, [] => .ok .top
    | some .neg, [f] => do pure (.neg (← decodeForm f))
    | some .conj, [f, g] => do
      let left ← decodeForm f
      let right ← decodeForm g
      pure (.conj left right)
    | some .box, [.atom b, f] => do pure (.box ⟨b⟩ (← decodeForm f))
    | some .dia, [.atom b, f] => do pure (.dia ⟨b⟩ (← decodeForm f))
    | _, _ => malformed "formula"
  | _ => malformed "formula"
termination_by sizeOf e

@[simp] theorem decodeForm_encode (f : SForm) :
    decodeForm (encodeForm f) = .ok f := by
  induction f <;> simp_all [encodeForm, decodeForm, tagged]

def encodePosed (p : Posed) : Sx := tagged .pose [.atom p.context.name, encodeForm p.form]

def decodePosed (e : Sx) : Except Error Posed :=
  match head e with
  | some (.pose, [.atom ctx, f]) => do pure ⟨⟨ctx⟩, ← decodeForm f⟩
  | _ => malformed "posed-query"

@[simp] theorem decodePosed_encode (p : Posed) :
    decodePosed (encodePosed p) = .ok p := by
  simp [encodePosed, decodePosed]

def encodeDocument (d : Document) : Sx :=
  tagged .document [.atom version, tagged .bridges (d.bridges.map encodeBridgeDecl),
    tagged .queries (d.queries.map encodePosed)]

/-- The version is read before the section layout, so a later version reports
`unsupportedVersion` whatever sections it carries. -/
def decodeDocument (e : Sx) : Except Error Document :=
  match head e with
  | some (.document, .atom v :: rest) =>
    if v = version then
      match rest with
      | [bs, qs] => do
        let bridges ← decodeList decodeBridgeDecl (← sectionItems .bridges bs)
        let queries ← decodeList decodePosed (← sectionItems .queries qs)
        pure ⟨bridges, queries⟩
      | _ => malformed "document"
    else .error ⟨.unsupportedVersion, v⟩
  | _ => malformed "document"

/-- Full structured round trip, including nested terms, formulas, and all lists. -/
@[simp] theorem decodeDocument_encode (d : Document) :
    decodeDocument (encodeDocument d) = .ok d := by
  simp [encodeDocument, decodeDocument]

/-- Distinct structured documents cannot collapse to one wire token tree. -/
theorem encodeDocument_injective : Function.Injective encodeDocument := by
  intro a b h
  have hd := congrArg decodeDocument h
  simpa using hd

/-- Canonical S-expression text, using the existing UTF-8/escape convention. -/
def print (d : Document) : String := Lara.Driver.printSx (encodeDocument d)

/-- Read exactly one document; source locations are retained for syntax errors. -/
def parse (text : String) : Except Error Document :=
  match Lara.Driver.parseWire text with
  | .error detail => .error ⟨.syntax, detail⟩
  | .ok e => decodeDocument e

end Lara.PW.Wire
