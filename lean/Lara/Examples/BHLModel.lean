import Lara.BHL.ModelLaws

namespace Lara.BHL.ModelExamples

/-- These symbolic events exercise model snapshots. Program execution and
statistical result computation are defined in their owning later stages. -/
inductive Command where
  | test : DatasetId → TestId → Command
  | idle
  deriving DecidableEq, Repr

def result : Variable .integer .observable := ⟨⟨0⟩⟩
def hidden : Variable .boolean .invisible := ⟨⟨0⟩⟩
def y : DatasetId := ⟨0⟩
def z : DatasetId := ⟨1⟩
def test : TestId := ⟨0⟩
def datasets : DatasetId → Nat := fun _ => 7

def initialMemory (hiddenValue : Bool) : Memory :=
  (Memory.empty.update result (some 1)).update hidden (some hiddenValue)

def initial (hiddenValue : Bool) : World Nat Command :=
  World.start (initialMemory hiddenValue) datasets

/-- Append a test-accounting snapshot using the actual canonical ledger update. -/
def recordSnapshot (world : World Nat Command) (name : DatasetId) : World Nat Command :=
  world.extend { world.current with
    history := world.current.history.record (world.current.datasets name) test
    action := .command (.test name test) }

def single : World Nat Command := recordSnapshot (initial false) y
def repeated : World Nat Command := recordSnapshot single z

/-- A test-only dynamics: ordinary primitives account for tests, and this
example has no sampling transitions. Later statistical instances supply their
own independent population and sampling constraints. -/
def dynamics : Dynamics Nat Command where
  initial := fun _ _ => True
  command := fun command visible => match command with
    | .test name testId => some (visible, {(visible.datasets name, testId)})
    | .idle => some (visible, 0)
  sampling := fun _ _ _ _ _ => False

def inhabitedModel : Model Nat Command :=
  ⟨dynamics, ⟨(initialMemory false).hidden,
    ⟨(initialMemory false).observable, datasets⟩, trivial⟩⟩

 theorem model_inhabited : Nonempty inhabitedModel.ValidWorld :=
  inhabitedModel.validWorld_nonempty

 theorem initial_admitted (bit : Bool) : Admitted dynamics (initial bit) := by
  simpa [initial, Memory.assemble_projections] using
    admitted_start dynamics ⟨(initialMemory bit).observable, datasets⟩
      (initialMemory bit).hidden trivial

 theorem recordSnapshot_admitted {world : World Nat Command}
    (h : Admitted dynamics world) (name : DatasetId) :
    Admitted dynamics (recordSnapshot world name) := by
  apply admitted_extend h
  · exact admitted_current_hidden h
  · change ∃ delta,
      dynamics.command (.test name test) world.current.visible =
        some (world.current.visible, delta) ∧
      History.record world.current.history (world.current.datasets name) test =
        world.current.history + delta
    refine ⟨{(world.current.datasets name, test)}, rfl, ?_⟩
    exact (Multiset.singleton_add _ _).symm.trans (Multiset.add_comm _ _)

 theorem single_admitted : Admitted dynamics single :=
  recordSnapshot_admitted (initial_admitted false) y

 theorem repeated_admitted : Admitted dynamics repeated :=
  recordSnapshot_admitted single_admitted z

 theorem lawful_prefix : Admitted dynamics (repeated.prefix 1) :=
  admitted_prefix repeated_admitted 1

 theorem initial_has_defined_result (bit : Bool) :
    (initial bit).current.memory.read result = some 1 := by
  simp [initial, initialMemory, result, hidden, Memory.read, Memory.update]

 theorem alias_names_distinct : y ≠ z := by decide

 theorem aliases_have_equal_values : datasets y = datasets z := rfl

 theorem alias_count_one :
    historyCount single.current.datasets single.current.history y test = 1 ∧
      historyCount single.current.datasets single.current.history z test = 1 := by
  constructor <;> simp [single, recordSnapshot, initial, datasets, historyCount,
    History.count, History.record]

 theorem repeated_count_two :
    historyCount repeated.current.datasets repeated.current.history y test = 2 ∧
      historyCount repeated.current.datasets repeated.current.history z test = 2 := by
  constructor <;> simp [repeated, single, recordSnapshot, initial, datasets, historyCount,
    History.count, History.record]

 theorem same_final_memory : single.current.memory = repeated.current.memory := by
  simp [single, repeated, recordSnapshot]

 theorem different_histories : single.current.history ≠ repeated.current.history := by
  simp only [repeated, recordSnapshot, World.extend_current]
  exact (History.record_ne_self _ _ _).symm

 theorem same_memory_different_observations :
    single.current.memory = repeated.current.memory ∧ ¬ Accessible single repeated := by
  refine ⟨same_final_memory, ?_⟩
  intro h
  exact different_histories (accessible_history_eq h)

 theorem reassignment_changes_lookup_not_ledger :
    historyCount (Function.update single.current.datasets y 8) single.current.history y test = 0 ∧
      historyCount (Function.update single.current.datasets y 8) single.current.history z test = 1 := by
  constructor
  · simp [single, recordSnapshot, initial, datasets, historyCount, History.count, History.record]
  · simp [single, recordSnapshot, initial, datasets, historyCount, History.count, History.record,
      y, z, Function.update]

 theorem hidden_alternatives_accessible : Accessible (initial false) (initial true) := by
  have hm : (fun s id => initialMemory false s .observable id) =
      (fun s id => initialMemory true s .observable id) := by
    funext s id
    simp [initialMemory, Memory.update, hidden]
  simpa [Accessible, observeWorld, World.trace, initial, World.start, observeState] using
    congrArg (fun memory => [Observation.mk memory datasets 0
      (.initial : Action Nat Command)]) hm

 theorem hidden_alternatives_different :
    (initial false).current.memory.read hidden ≠ (initial true).current.memory.read hidden := by
  simp [initial, initialMemory]

 theorem histories_initially_empty (bit : Bool) : (initial bit).current.history = 0 := rfl

 theorem repeated_combination_keeps_multiplicity :
    History.count (decomposeTests (.conj (.leaf 7 test) (.leaf 7 test))) 7 test = 2 :=
  decompose_repeated_pair_conj 7 test

def productList : Variable (.list (.product .integer .boolean)) .observable := ⟨⟨2⟩⟩
def realValue : Variable .real .observable := ⟨⟨3⟩⟩
def population : Variable (.population .real) .invisible := ⟨⟨4⟩⟩

noncomputable def mathematicalMemory : Memory :=
  ((Memory.empty.update productList (some [(3, true), (4, false)])).update
    realValue (some 0)).update population (some realDiracTest.nullLaw)

 theorem mathematical_carriers_defined :
    mathematicalMemory.read productList = some [(3, true), (4, false)] ∧
    mathematicalMemory.read realValue = some 0 ∧
    mathematicalMemory.read population = some realDiracTest.nullLaw := by
  simp [mathematicalMemory, productList, realValue, population, Memory.read, Memory.update]

def jointPopulation : Variable (.population (.product .real .real)) .invisible := ⟨⟨5⟩⟩
def listPopulation : Variable (.population (.list .real)) .invisible := ⟨⟨6⟩⟩
def booleanPopulation : Variable (.population .boolean) .invisible := ⟨⟨7⟩⟩

noncomputable def jointLaw : Value (.population (.product .real .real)) :=
  diracProbability ((0 : ℝ), (1 : ℝ))

noncomputable def listLaw : Value (.population (.list .real)) :=
  @diracProbability (Value (.list .real)) (valueMeasurableSpace (.list .real)) [0, 1]

noncomputable def generalPopulationMemory : Memory :=
  ((Memory.empty.update jointPopulation (some jointLaw)).update
    listPopulation (some listLaw)).update booleanPopulation (some (diracProbability false))

 theorem joint_list_boolean_laws_inhabit_memory :
    generalPopulationMemory.read jointPopulation = some jointLaw ∧
    generalPopulationMemory.read listPopulation = some listLaw ∧
    generalPopulationMemory.read booleanPopulation = some (diracProbability false) := by
  simp [generalPopulationMemory, jointPopulation, listPopulation, booleanPopulation,
    Memory.read, Memory.update]

 theorem joint_law_normalized :
    (jointLaw : MeasureTheory.Measure (ℝ × ℝ)) Set.univ = 1 :=
  value_population_mass (.product .real .real) jointLaw

end Lara.BHL.ModelExamples
