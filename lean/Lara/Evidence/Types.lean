import Lara.Prop

namespace Lara.Evidence

/-- `do`-notation lowers to `Bind.bind` on the `Except` instance, and this
toolchain's simplifier does not otherwise reduce a bind whose scrutinee is a
literal constructor.  Both equations hold definitionally; registering them
keeps every do-block proof in this model a `simp`-level argument instead of a
hand unfolding of the monad instance. -/
@[simp] theorem except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    bind (Except.error e : Except ε α) f = Except.error e := rfl

@[simp] theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    bind (Except.ok a : Except ε α) f = f a := rfl

inductive LeafCheckerId where | csvRow | jsonPointer deriving DecidableEq, Repr
structure CheckerVersion where
  val : Int
  deriving DecidableEq, Repr
structure ObjectId where
  val : String
  deriving DecidableEq, Repr
structure ColumnName where
  val : String
  deriving DecidableEq, Repr
structure JsonToken where
  val : String
  deriving DecidableEq, Repr
abbrev JsonPath := List JsonToken
inductive TermEncoding where | decimal | text | decimalLine deriving DecidableEq, Repr
structure CsvSelector where
  column : ColumnName
  encoding : TermEncoding
  deriving DecidableEq, Repr
structure JsonSelector where
  path : JsonPath
  encoding : TermEncoding
  deriving DecidableEq, Repr
inductive ExtractionRequest where
  | csvRowRequest : CheckerVersion → ObjectId → ColumnName → String →
      List CsvSelector → String → ExtractionRequest
  | jsonPointerRequest : CheckerVersion → ObjectId → List JsonSelector → String → ExtractionRequest
  deriving DecidableEq, Repr

def checkerName : LeafCheckerId → String
  | .csvRow => "csv-row"
  | .jsonPointer => "json-pointer"
def encodingName : TermEncoding → String
  | .decimal => "decimal"
  | .text => "text"
  | .decimalLine => "decimal-line"
theorem checkerName_injective : Function.Injective checkerName := by
  intro a b; cases a <;> cases b <;> simp [checkerName]
theorem encodingName_injective : Function.Injective encodingName := by
  intro a b; cases a <;> cases b <;> simp [encodingName]
def requestChecker : ExtractionRequest → LeafCheckerId
  | .csvRowRequest .. => .csvRow
  | .jsonPointerRequest .. => .jsonPointer
def requestVersion : ExtractionRequest → CheckerVersion
  | .csvRowRequest v .. => v
  | .jsonPointerRequest v .. => v
def requestObjects : ExtractionRequest → List ObjectId
  | .csvRowRequest _ o .. => [o]
  | .jsonPointerRequest _ o .. => [o]
theorem requestObjects_singleton (r : ExtractionRequest) :
    ∃ o, requestObjects r = [o] := by cases r <;> exact ⟨_, rfl⟩

structure PackagePath where
  val : String
  deriving DecidableEq, Repr
structure Sha256 where
  val : String
  deriving DecidableEq, Repr

/-- Manifest metadata is not membership assurance. Only a successful snapshot lookup
supplies a captured object. Concrete path validation, OS capture and SHA are outside
this finite immutable model. -/
structure ObjectMeta where
  id : ObjectId
  path : PackagePath
  length : Nat
  digest : Sha256
  deriving DecidableEq, Repr
structure CsvTable where
  header : List ColumnName
  rows : List (List String)
  deriving DecidableEq, Repr
mutual
  inductive JsonValue where
    | object : JsonEntries → JsonValue
    | array : JsonValues → JsonValue
    | string : String → JsonValue
    | number : String → JsonValue
    | bool : Bool → JsonValue
    | null : JsonValue
  inductive JsonEntries where
    | nil : JsonEntries
    | cons : JsonToken → JsonValue → JsonEntries → JsonEntries
  inductive JsonValues where
    | nil : JsonValues
    | cons : JsonValue → JsonValues → JsonValues
end
deriving instance DecidableEq for JsonValue, JsonEntries, JsonValues
inductive Payload where
  | csv : CsvTable → Payload
  | json : JsonValue → Payload
  deriving DecidableEq
structure CapturedObject where
  metadata : ObjectMeta
  payload : Payload
  deriving DecidableEq
abbrev Snapshot := List (ObjectId × Except String CapturedObject)
abbrev Registry := ExtractionRequest → List CapturedObject → Except String Lara.Atom

end Lara.Evidence
