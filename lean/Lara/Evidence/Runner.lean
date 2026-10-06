import Lara.Evidence.Extract

namespace Lara.Evidence
open Lara

def lookup (s : Snapshot) (id : ObjectId) : Except String CapturedObject :=
  match s.find? (fun entry => entry.1 == id) with
  | none => .error "missingdep"
  | some entry => match entry.2 with
    | .error reason => .error reason
    | .ok object => if object.metadata.id = id then .ok object else .error "metadata"

theorem lookup_id {s id object} (h : lookup s id = .ok object) : object.metadata.id = id := by
  unfold lookup at h
  cases hf : s.find? (fun entry => entry.1 == id) with
  | none => simp [hf] at h
  | some entry =>
    cases he : entry.2 with
    | error e => simp [hf, he] at h
    | ok found =>
      by_cases hi : found.metadata.id = id
      · simp [hf, he, hi] at h; subst object; exact hi
      · simp [hf, he, hi] at h

def supply (s : Snapshot) : List ObjectId → Except String (List CapturedObject)
  | [] => .ok []
  | id :: ids => do
      let object ← lookup s id
      let rest ← supply s ids
      .ok (object :: rest)

structure RunResult where
  proposition : Atom
  dependencies : List ObjectMeta
  deriving DecidableEq

def run (s : Snapshot) (registry : Registry) (r : ExtractionRequest) : Except String RunResult := do
  let objects ← supply s (requestObjects r)
  let proposition ← registry r objects
  .ok ⟨proposition, objects.map (·.metadata)⟩

/-- Runner-owned metadata is the exact ordered list supplied to the pure registry. -/
theorem run_dependencies {s registry r result} (h : run s registry r = .ok result) :
    ∃ objects, supply s (requestObjects r) = .ok objects ∧
      registry r objects = .ok result.proposition ∧ result.dependencies = objects.map (·.metadata) := by
  unfold run at h
  cases hs : supply s (requestObjects r) with
  | error e => simp [hs, except_bind_error] at h
  | ok objects =>
    cases hr : registry r objects with
    | error e => simp [hs, hr, except_bind_error] at h
    | ok proposition =>
      simp only [hs, hr, except_bind_ok] at h
      cases h
      exact ⟨objects, rfl, hr, rfl⟩

theorem supply_membership {s ids objects} (h : supply s ids = .ok objects) :
    ∀ object ∈ objects, ∃ id ∈ ids, lookup s id = .ok object := by
  induction ids generalizing objects with
  | nil => simp [supply] at h; subst objects; simp
  | cons id ids ih =>
    cases hl : lookup s id with
    | error e => simp [supply, hl, except_bind_error] at h
    | ok object =>
      cases hs : supply s ids with
      | error e => simp [supply, hl, hs, except_bind_error] at h
      | ok rest =>
        simp only [supply, hl, hs, except_bind_ok] at h
        injection h with hlist
        subst objects
        intro o ho
        rcases List.mem_cons.mp ho with rfl | ho
        · exact ⟨id, List.mem_cons_self, hl⟩
        · rcases ih hs o ho with ⟨i, hi, hlo⟩
          exact ⟨i, List.mem_cons_of_mem _ hi, hlo⟩

theorem run_snapshot_membership {s registry r result} (h : run s registry r = .ok result) :
    ∀ metadata ∈ result.dependencies,
      ∃ id ∈ requestObjects r, ∃ object,
        lookup s id = .ok object ∧ object.metadata = metadata := by
  rcases run_dependencies h with ⟨objects, hs, _, hd⟩
  rw [hd]
  intro metadata hm
  rcases List.mem_map.mp hm with ⟨object, ho, rfl⟩
  rcases supply_membership hs object ho with ⟨id, hi, hl⟩
  exact ⟨id, hi, object, hl, rfl⟩

/-- Locality is equality of actual immutable lookup results, including capture
errors and metadata, not an assumption that equal hashes imply equal bytes. -/
def LocalOn (ids : List ObjectId) (s t : Snapshot) : Prop :=
  ∀ id ∈ ids, lookup s id = lookup t id

theorem supply_locality {ids s t} (h : LocalOn ids s t) : supply s ids = supply t ids := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
    have hh := h id List.mem_cons_self
    have ht : LocalOn ids s t := fun i hi => h i (List.mem_cons_of_mem _ hi)
    simp [supply, hh, ih ht]

theorem run_locality {r s t registry} (h : LocalOn (requestObjects r) s t) :
    run s registry r = run t registry r := by
  simp [run, supply_locality h]

theorem missing_dependency (s : Snapshot) (registry : Registry) (r : ExtractionRequest)
    (id : ObjectId) (h : requestObjects r = [id]) (hm : lookup s id = .error "missingdep") :
    run s registry r = .error "missingdep" := by
  simp only [run, h, supply, hm, except_bind_error]

theorem run_registry_replacement {s r first second}
    (h : ∀ objects, supply s (requestObjects r) = .ok objects → first r objects = second r objects) :
    run s first r = run s second r := by
  unfold run
  cases hs : supply s (requestObjects r) with
  | error e => rfl
  | ok objects => simp only [except_bind_ok, h objects hs]

theorem supply_exact_ids {s ids objects} (h : supply s ids = .ok objects) :
    objects.map (fun object => object.metadata.id) = ids := by
  induction ids generalizing objects with
  | nil => simp [supply] at h; subst objects; rfl
  | cons id ids ih =>
    cases hl : lookup s id with
    | error e => simp [supply, hl, except_bind_error] at h
    | ok object =>
      cases ht : supply s ids with
      | error e => simp [supply, hl, ht, except_bind_error] at h
      | ok tail =>
        simp only [supply, hl, ht, except_bind_ok] at h
        injection h with hlist
        subst objects
        simp only [List.map_cons, lookup_id hl, ih ht]

theorem run_exact_declared_dependencies {s registry request result}
    (h : run s registry request = .ok result) :
    result.dependencies.map (·.id) = requestObjects request := by
  rcases run_dependencies h with ⟨objects, hs, _, hd⟩
  rw [hd]
  simpa [List.map_map, Function.comp_def] using supply_exact_ids hs

theorem run_deterministic {s registry r a b}
    (ha : run s registry r = a) (hb : run s registry r = b) : a = b := ha.symm.trans hb

end Lara.Evidence
