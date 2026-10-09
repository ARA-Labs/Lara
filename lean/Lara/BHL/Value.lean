import Lara.BHL.Types
import Lara.BHL.Numeric
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
Actual denotations of BHL value sorts and an intrinsically sorted memory.
A cell is identified jointly by its sort, visibility, and symbolic variable id.
Every cell may be undefined; renaming changes ids consistently, never values.
-/

namespace Lara.BHL

/-- The finite-list sigma algebra observes every optional coordinate. It uses
the sample sigma algebra rather than making uncountable real lists discrete. -/
abbrev listMeasurableSpace {α : Type} (m : MeasurableSpace α) : MeasurableSpace (List α) :=
  ⨆ n : Nat, (m.map some).comap (fun values : List α => values[n]?)

/-- Construct each sample carrier together with its sigma algebra. Population
sorts include joint, list-valued, and recursively distribution-valued laws. -/
noncomputable abbrev valueCarrier : ValueSort → (Σ α : Type, MeasurableSpace α)
  | .boolean => ⟨Bool, inferInstance⟩
  | .integer => ⟨Int, inferInstance⟩
  | .real => ⟨ℝ, inferInstance⟩
  | .population sample =>
      let carrier := valueCarrier sample
      letI : MeasurableSpace carrier.1 := carrier.2
      ⟨MeasureTheory.ProbabilityMeasure carrier.1,
        (inferInstance : MeasurableSpace (MeasureTheory.Measure carrier.1)).comap Subtype.val⟩
  | .product left right =>
      let l := valueCarrier left
      let r := valueCarrier right
      ⟨l.1 × r.1, l.2.prod r.2⟩
  | .list element =>
      let carrier := valueCarrier element
      ⟨List carrier.1, listMeasurableSpace carrier.2⟩

/-- Actual mathematical values; undefinedness belongs to memory, not this type. -/
abbrev Value (sort : ValueSort) : Type := (valueCarrier sort).1

noncomputable instance valueMeasurableSpace (sort : ValueSort) : MeasurableSpace (Value sort) :=
  (valueCarrier sort).2

 theorem measurable_list_coordinate {α : Type} (m : MeasurableSpace α) (n : Nat) :
    @Measurable (List α) (Option α) (listMeasurableSpace m) (m.map some)
      (fun values => values[n]?) :=
  Measurable.of_comap_le (le_iSup (fun index : Nat =>
    (m.map some).comap (fun values : List α => values[index]?)) n)

 theorem value_population_carrier (sample : ValueSort) :
    Value (.population sample) = MeasureTheory.ProbabilityMeasure (Value sample) := rfl

 theorem value_measurable_product (left right : ValueSort) :
    valueMeasurableSpace (.product left right) =
      (valueMeasurableSpace left).prod (valueMeasurableSpace right) := rfl

 theorem value_population_mass (sample : ValueSort) (law : Value (.population sample)) :
    (law : MeasureTheory.Measure (Value sample)) Set.univ = 1 :=
  MeasureTheory.measure_univ

/-- This witnesses value carriers only; undefined memory cells remain `none`. -/
noncomputable def valueDefault : (sort : ValueSort) → Value sort
  | .boolean => false
  | .integer => 0
  | .real => 0
  | .population sample => diracProbability (valueDefault sample)
  | .product left right => (valueDefault left, valueDefault right)
  | .list _ => []

 theorem value_nonempty (sort : ValueSort) : Nonempty (Value sort) := ⟨valueDefault sort⟩

/-- Undefinedness is explicit at every sort, including products and lists. -/
def Memory := (s : ValueSort) → Visibility → VarId → Option (Value s)

abbrev ObservableMemory := (s : ValueSort) → VarId → Option (Value s)
abbrev HiddenMemory := (s : ValueSort) → VarId → Option (Value s)

namespace Variable

/-- A bijection changes only the symbolic name of a typed variable. -/
def rename (ρ : VarId ≃ VarId) {s : ValueSort} {v : Visibility}
    (x : Variable s v) : Variable s v :=
  ⟨ρ x.id⟩

@[simp] theorem rename_id {s : ValueSort} {v : Visibility} (x : Variable s v) :
    rename (Equiv.refl VarId) x = x := by
  cases x
  rfl

 theorem rename_comp (ρ σ : VarId ≃ VarId) {s : ValueSort} {v : Visibility}
    (x : Variable s v) :
    rename σ (rename ρ x) = rename (ρ.trans σ) x := rfl

@[simp] theorem rename_symm (ρ : VarId ≃ VarId) {s : ValueSort} {v : Visibility}
    (x : Variable s v) : rename ρ.symm (rename ρ x) = x := by
  cases x
  simp [rename]

end Variable

namespace Memory

/-- The initial memory has no defined bindings. -/
def empty : Memory := fun _ _ _ => none

/-- A typed variable can read only the carrier at its own sort and visibility. -/
def read (memory : Memory) {s : ValueSort} {v : Visibility}
    (x : Variable s v) : Option (Value s) :=
  memory s v x.id

def observable (memory : Memory) : ObservableMemory := fun s id => memory s .observable id

def hidden (memory : Memory) : HiddenMemory := fun s id => memory s .invisible id

def assemble (visible : ObservableMemory) (ordinaryHidden : HiddenMemory) : Memory :=
  fun s visibility id => match visibility with
    | .observable => visible s id
    | .invisible => ordinaryHidden s id

@[simp] theorem observable_assemble (visible : ObservableMemory) (h : HiddenMemory) :
    (assemble visible h).observable = visible := rfl

@[simp] theorem hidden_assemble (visible : ObservableMemory) (h : HiddenMemory) :
    (assemble visible h).hidden = h := rfl

 theorem assemble_projections (memory : Memory) :
    assemble memory.observable memory.hidden = memory := by
  funext s visibility id
  cases visibility <;> rfl

@[simp] theorem read_empty {s : ValueSort} {v : Visibility} (x : Variable s v) :
    empty.read x = none := rfl

/-- Equality of every typed read determines equality of memories. -/
@[ext] theorem ext {left right : Memory}
    (h : ∀ (s : ValueSort) (v : Visibility) (x : Variable s v),
      left.read x = right.read x) : left = right := by
  funext s v id
  exact h s v ⟨id⟩

/-- Write or clear exactly one cell. Matching sorts transport the optional value;
matching names at another sort or visibility are independent cells. -/
def update (memory : Memory) {s : ValueSort} {v : Visibility}
    (x : Variable s v) (value : Option (Value s)) : Memory :=
  fun t w id =>
    if hsort : s = t then
      if v = w ∧ x.id = id then hsort ▸ value else memory t w id
    else memory t w id

@[simp] theorem read_update_self (memory : Memory) {s : ValueSort} {v : Visibility}
    (x : Variable s v) (value : Option (Value s)) :
    (memory.update x value).read x = value := by
  simp [read, update]

/-- The exact different-cell condition: at least one of sort, visibility, or id differs. -/
 theorem read_update_other (memory : Memory) {s t : ValueSort} {v w : Visibility}
    (x : Variable s v) (value : Option (Value s)) (y : Variable t w)
    (h : s ≠ t ∨ v ≠ w ∨ x.id ≠ y.id) :
    (memory.update x value).read y = memory.read y := by
  by_cases hsort : s = t
  · rcases h with h | h | h
    · exact (h hsort).elim
    · simp [read, update, hsort, h]
    · simp [read, update, hsort, h]
  · simp [read, update, hsort]

/-- Observable writes preserve every invisible read, even at the same sort and id. -/
 theorem read_update_invisible (memory : Memory) {s t : ValueSort}
    (x : Variable s .observable) (value : Option (Value s))
    (y : Variable t .invisible) :
    (memory.update x value).read y = memory.read y :=
  read_update_other memory x value y (Or.inr (Or.inl (by decide)))

/-- A second write to the same typed cell completely supersedes the first. -/
@[simp] theorem update_overwrite (memory : Memory) {s : ValueSort} {v : Visibility}
    (x : Variable s v) (first second : Option (Value s)) :
    (memory.update x first).update x second = memory.update x second := by
  funext t w id
  by_cases hsort : s = t
  · by_cases hcell : v = w ∧ x.id = id
    · simp [update, hsort, hcell]
    · simp [update, hsort, hcell]
  · simp [update, hsort]

/-- The target read acquires the written optional value, and a changed read must
have exactly the target's sort, visibility, and id. This rules out cross-sort writes. -/
 theorem memory_update_typed (memory : Memory) {s : ValueSort} {v : Visibility}
    (x : Variable s v) (value : Option (Value s)) :
    (memory.update x value).read x = value ∧
      ∀ (t : ValueSort) (w : Visibility) (y : Variable t w),
        (memory.update x value).read y ≠ memory.read y →
          s = t ∧ v = w ∧ x.id = y.id := by
  refine ⟨read_update_self memory x value, ?_⟩
  intro t w y hchanged
  by_cases hsort : s = t
  · by_cases hvisibility : v = w
    · by_cases hid : x.id = y.id
      · exact ⟨hsort, hvisibility, hid⟩
      · exact (hchanged
          (read_update_other memory x value y (Or.inr (Or.inr hid)))).elim
    · exact (hchanged
        (read_update_other memory x value y (Or.inr (Or.inl hvisibility)))).elim
  · exact (hchanged (read_update_other memory x value y (Or.inl hsort))).elim

/-- Pull back by the inverse bijection so a renamed cell retains its binding. -/
def rename (ρ : VarId ≃ VarId) (memory : Memory) : Memory :=
  fun s v id => memory s v (ρ.symm id)

@[simp] theorem read_rename (ρ : VarId ≃ VarId) (memory : Memory)
    {s : ValueSort} {v : Visibility} (x : Variable s v) :
    (rename ρ memory).read (Variable.rename ρ x) = memory.read x := by
  simp [read, rename, Variable.rename]

/-- Consistent renaming preserves defined and undefined typed bindings in both directions. -/
 theorem rename_binding_preserves (ρ : VarId ≃ VarId) (memory : Memory)
    {s : ValueSort} {v : Visibility} (x : Variable s v) (value : Option (Value s)) :
    (rename ρ memory).read (Variable.rename ρ x) = value ↔ memory.read x = value := by
  rw [read_rename]

@[simp] theorem rename_id (memory : Memory) :
    rename (Equiv.refl VarId) memory = memory := rfl

 theorem rename_comp (ρ σ : VarId ≃ VarId) (memory : Memory) :
    rename σ (rename ρ memory) = rename (ρ.trans σ) memory := rfl

@[simp] theorem rename_symm (ρ : VarId ≃ VarId) (memory : Memory) :
    rename ρ.symm (rename ρ memory) = memory := by
  funext s v id
  simp [rename]

@[simp] theorem rename_empty (ρ : VarId ≃ VarId) : rename ρ empty = empty := rfl

/-- Renaming commutes with typed writes, including clearing a binding. -/
 theorem rename_update (ρ : VarId ≃ VarId) (memory : Memory)
    {s : ValueSort} {v : Visibility} (x : Variable s v) (value : Option (Value s)) :
    rename ρ (memory.update x value) =
      (rename ρ memory).update (Variable.rename ρ x) value := by
  funext t w id
  have hid : x.id = ρ.symm id ↔ ρ x.id = id := by
    constructor
    · intro h
      calc
        ρ x.id = ρ (ρ.symm id) := congrArg ρ h
        _ = id := ρ.apply_symm_apply id
    · intro h
      calc
        x.id = ρ.symm (ρ x.id) := (ρ.symm_apply_apply x.id).symm
        _ = ρ.symm id := congrArg ρ.symm h
  simp [rename, update, Variable.rename, hid]

end Memory

end Lara.BHL
