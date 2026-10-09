import Lara.Evidence.Runner
import Lara.Presentation
import Init.Data.String.Lemmas.Pattern.TakeDrop.Pred

namespace Lara.Evidence
open Lara
open Lara.Presentation (Leaf LeafKind Provenance)

abbrev EvidencePolicy := List (LeafCheckerId × CheckerVersion)

def manifestObject (manifest : List ObjectMeta) (id : ObjectId) : Option ObjectMeta :=
  manifest.find? (fun m => m.id == id)
private def referencePathRuntime (ref : String) : String :=
  (ref.takeWhile (fun c => c != '#')).copy

/-- The path before the first fragment marker. The kernel specification is
transparent; compiled code scans a slice and copies only the selected prefix. -/
@[implemented_by referencePathRuntime]
def referencePath (ref : String) : String :=
  String.ofList (ref.toList.takeWhile (fun c => c != '#'))

private theorem takeWhile_prefix (predicate : Char → Bool) (headChars tailChars : List Char)
    (safe : headChars.all predicate = true) (stopped : tailChars.head?.any predicate = false) :
    (headChars ++ tailChars).takeWhile predicate = headChars := by
  induction headChars with
  | nil =>
      cases tailChars with
      | nil => rfl
      | cons first rest =>
          change predicate first = false at stopped
          simp [List.takeWhile, stopped]
  | cons first rest ih =>
      change (predicate first && rest.all predicate) = true at safe
      have both : predicate first = true ∧ rest.all predicate = true := by simpa using safe
      simp [List.takeWhile, both.1, ih both.2]

/-- The allocation-efficient compiled implementation has the same prefix
meaning as the transparent kernel definition for every Unicode string. -/
theorem referencePath_eq_runtime (ref : String) :
    referencePath ref = (ref.takeWhile (fun c => c != '#')).copy := by
  let predicate : Char → Bool := fun c => c != '#'
  have safe : (ref.takeWhile predicate).copy.toList.all predicate = true := by
    simpa only [String.Slice.all_bool_eq] using
      (String.all_takeWhile (s := ref) (pat := predicate))
  have stopped : (ref.dropWhile predicate).copy.toList.head?.any predicate = false := by
    simpa only [String.Slice.startsWith_bool_eq_head?] using
      (String.startsWith_dropWhile (s := ref) (pat := predicate))
  have partition : ref.toList =
      (ref.takeWhile predicate).copy.toList ++ (ref.dropWhile predicate).copy.toList := by
    simpa only [String.toList_append] using
      congrArg String.toList (String.takeWhile_append_dropWhile (s := ref) (pat := predicate)).symm
  unfold referencePath
  change String.ofList (ref.toList.takeWhile predicate) = _
  rw [partition, takeWhile_prefix predicate _ _ safe stopped]
  simp [predicate]

theorem referencePath_without_fragment (ref : String)
    (safe : ref.toList.all (fun c => c != '#') = true) : referencePath ref = ref := by
  unfold referencePath
  have equal := takeWhile_prefix (fun c => c != '#') ref.toList [] safe (by rfl)
  simpa using congrArg String.ofList equal

theorem referencePath_before_fragment (headChars tailChars : List Char)
    (safe : headChars.all (fun c => c != '#') = true) :
    referencePath (String.ofList (headChars ++ '#' :: tailChars)) = String.ofList headChars := by
  unfold referencePath
  simp only [String.toList_ofList]
  rw [takeWhile_prefix (fun c => c != '#') headChars ('#' :: tailChars) safe (by rfl)]

def requestReferenceValid (manifest : List ObjectMeta) (leaf : Leaf) (id : ObjectId) : Prop :=
  match manifestObject manifest id with
  | none => False
  | some metadata => ∃ ref ∈ leaf.refs, referencePath ref.val = metadata.path.val
instance (manifest : List ObjectMeta) (leaf : Leaf) (id : ObjectId) :
    Decidable (requestReferenceValid manifest leaf id) := by
  unfold requestReferenceValid
  split <;> infer_instance
/-- Independent binding specification; requests never contain expected output. -/
def RequestBound (policy : EvidencePolicy) (manifest : List ObjectMeta)
    (leaf : Leaf) (request : ExtractionRequest) : Prop :=
  leaf.kind = .certified ∧ leaf.extraction = some request ∧
  requestVersion request = ⟨1⟩ ∧
  (requestChecker request, requestVersion request) ∈ policy ∧
  leaf.provenance = .checker (checkerName (requestChecker request)) "1" ∧
  ∀ id ∈ requestObjects request, requestReferenceValid manifest leaf id
instance (policy : EvidencePolicy) (manifest : List ObjectMeta) (leaf : Leaf)
    (request : ExtractionRequest) : Decidable (RequestBound policy manifest leaf request) := by
  unfold RequestBound
  infer_instance

def BindingValid (policy : EvidencePolicy) (manifest : List ObjectMeta) (leaf : Leaf) : Prop :=
  match leaf.kind, leaf.extraction with
  | .certified, some request => RequestBound policy manifest leaf request
  | .certified, none => False
  | _, none => True
  | _, some _ => False
instance (policy : EvidencePolicy) (manifest : List ObjectMeta) (leaf : Leaf) :
    Decidable (BindingValid policy manifest leaf) := by
  unfold BindingValid
  split <;> infer_instance

def requestedIds (leaves : List Leaf) : List ObjectId :=
  leaves.flatMap fun leaf => leaf.extraction.toList.flatMap requestObjects

def requestedManifest (manifest : List ObjectMeta) (leaves : List Leaf) : List ObjectMeta :=
  manifest.filter (fun m => decide (m.id ∈ requestedIds leaves))

def CapturedValid (snapshot : Snapshot) (metadata : ObjectMeta) : Prop :=
  ∃ object, lookup snapshot metadata.id = .ok object ∧ object.metadata = metadata
instance (snapshot : Snapshot) (metadata : ObjectMeta) :
    Decidable (CapturedValid snapshot metadata) := by
  unfold CapturedValid
  cases h : lookup snapshot metadata.id with
  | error e => exact isFalse (by rintro ⟨o, ho, _⟩; cases ho)
  | ok o =>
    by_cases hm : o.metadata = metadata
    · exact isTrue ⟨o, rfl, hm⟩
    · exact isFalse (by rintro ⟨p, hp, hpm⟩; injection hp with hp'; subst hp'; exact hm hpm)

inductive Stage where | binding | capture | extraction deriving DecidableEq
structure AdmissionError where
  stage : Stage
  leaf : String
  object : Option ObjectId
  reason : String
  deriving DecidableEq
structure Judgment where
  leaf : String
  request : ExtractionRequest
  normalized : Atom
  dependencies : List ObjectMeta
  deriving DecidableEq

/-- First failing declaration in the supplied order. Capture receives manifest
order, binding/extraction receive leaf order; stages are never interleaved. -/
def firstInvalid (valid : α → Prop) [DecidablePred valid] : List α → Option α
  | [] => none
  | a :: rest => if valid a then firstInvalid valid rest else some a

theorem firstInvalid_none_iff (valid : α → Prop) [DecidablePred valid] (xs : List α) :
    firstInvalid valid xs = none ↔ ∀ x ∈ xs, valid x := by
  induction xs with
  | nil => simp [firstInvalid]
  | cons x xs ih =>
    by_cases hx : valid x <;> simp [firstInvalid, hx, ih]

theorem firstInvalid_prefix (valid : α → Prop) [DecidablePred valid] {xs : List α} {x : α}
    (h : firstInvalid valid xs = some x) :
    ∃ before after, xs = before ++ x :: after ∧ (∀ a ∈ before, valid a) ∧ ¬ valid x := by
  induction xs with
  | nil => simp [firstInvalid] at h
  | cons head rest ih =>
    by_cases hh : valid head
    · have ht : firstInvalid valid rest = some x := by simpa [firstInvalid, hh] using h
      rcases ih ht with ⟨before, after, heq, hv, hn⟩
      exact ⟨head :: before, after, by simp [heq],
        by intro a ha
           rcases List.mem_cons.mp ha with rfl | ha
           · exact hh
           · exact hv a ha, hn⟩
    · simp [firstInvalid, hh] at h
      subst x
      exact ⟨[], rest, rfl, by simp, hh⟩

def bindingObject (policy : EvidencePolicy) (manifest : List ObjectMeta) (leaf : Leaf) : Option ObjectId :=
  match leaf.kind, leaf.extraction with
  | .certified, some request =>
    if requestVersion request = ⟨1⟩ ∧
        (requestChecker request, requestVersion request) ∈ policy ∧
        leaf.provenance = .checker (checkerName (requestChecker request)) "1" then
      firstInvalid (requestReferenceValid manifest leaf) (requestObjects request)
    else none
  | _, _ => none

def bindingStage (policy : EvidencePolicy) (manifest : List ObjectMeta) (leaves : List Leaf) :
    Option AdmissionError :=
  (firstInvalid (BindingValid policy manifest) leaves).map fun leaf =>
    ⟨.binding, leaf.id.val, bindingObject policy manifest leaf, "binding"⟩
def firstReferencing (leaves : List Leaf) (id : ObjectId) : String :=
  ((leaves.find? fun leaf => decide (id ∈ leaf.extraction.toList.flatMap requestObjects)).map (·.id.val)).getD ""
def captureStage (snapshot : Snapshot) (manifest : List ObjectMeta) (leaves : List Leaf) :
    Option AdmissionError :=
  (firstInvalid (CapturedValid snapshot) (requestedManifest manifest leaves)).map fun metadata =>
    ⟨.capture, firstReferencing leaves metadata.id, some metadata.id,
      match lookup snapshot metadata.id with | .error e => e | .ok _ => "metadata"⟩

def replayLeaf (snapshot : Snapshot) (registry : Registry) (leaf : Leaf) :
    Except AdmissionError (List Judgment) :=
  match leaf.kind, leaf.extraction with
  | .certified, some request =>
    match run snapshot registry request with
    | .error reason => .error ⟨.extraction, leaf.id.val, none, reason⟩
    | .ok result =>
      if nf canonNum result.proposition = nf canonNum leaf.prop then
        .ok [⟨leaf.id.val, request, nf canonNum result.proposition, result.dependencies⟩]
      else .error ⟨.extraction, leaf.id.val, none, "mismatch"⟩
  | .certified, none => .error ⟨.binding, leaf.id.val, none, "binding"⟩
  | _, _ => .ok []

def replayLeaves (snapshot : Snapshot) (registry : Registry) : List Leaf → Except AdmissionError (List Judgment)
  | [] => .ok []
  | leaf :: rest => do
    let head ← replayLeaf snapshot registry leaf
    let tail ← replayLeaves snapshot registry rest
    .ok (head ++ tail)

/-- Declarative replay is built from actual immutable supply and registry
premises, independently of the executable replay/admission return equation. -/
inductive LeafReplayed (snapshot : Snapshot) (registry : Registry) : Leaf → List Judgment → Prop where
  | ordinary : leaf.kind ≠ .certified → LeafReplayed snapshot registry leaf []
  | certified : leaf.kind = .certified → leaf.extraction = some request →
      supply snapshot (requestObjects request) = .ok objects →
      registry request objects = .ok proposition →
      nf canonNum proposition = nf canonNum leaf.prop →
      LeafReplayed snapshot registry leaf
        [⟨leaf.id.val, request, nf canonNum proposition, objects.map (·.metadata)⟩]

inductive AllReplayed (snapshot : Snapshot) (registry : Registry) : List Leaf → List Judgment → Prop where
  | nil : AllReplayed snapshot registry [] []
  | cons : LeafReplayed snapshot registry leaf head → AllReplayed snapshot registry rest tail →
      AllReplayed snapshot registry (leaf :: rest) (head ++ tail)

structure Admitted (snapshot : Snapshot) (policy : EvidencePolicy) (manifest : List ObjectMeta)
    (registry : Registry) (leaves : List Leaf) (judgments : List Judgment) : Prop where
  bindings : ∀ leaf ∈ leaves, BindingValid policy manifest leaf
  capture : ∀ metadata ∈ requestedManifest manifest leaves, CapturedValid snapshot metadata
  replay : AllReplayed snapshot registry leaves judgments

def admit (snapshot : Snapshot) (policy : EvidencePolicy) (manifest : List ObjectMeta)
    (registry : Registry) (leaves : List Leaf) : Except AdmissionError (List Judgment) :=
  match bindingStage policy manifest leaves with
  | some error => .error error
  | none => match captureStage snapshot manifest leaves with
    | some error => .error error
    | none => replayLeaves snapshot registry leaves

theorem replayLeaf_iff {snapshot registry leaf judgments} :
    replayLeaf snapshot registry leaf = .ok judgments ↔ LeafReplayed snapshot registry leaf judgments := by
  constructor
  · intro h
    by_cases hk : leaf.kind = .certified
    · cases hr : leaf.extraction with
      | none => simp [replayLeaf, hk, hr] at h
      | some request =>
        cases hs : supply snapshot (requestObjects request) with
        | error reason => simp [replayLeaf, hk, hr, run, hs] at h
        | ok objects =>
          cases hg : registry request objects with
          | error reason => simp [replayLeaf, hk, hr, run, hs, hg] at h
          | ok proposition =>
            by_cases he : nf canonNum proposition = nf canonNum leaf.prop
            · have hval : replayLeaf snapshot registry leaf =
                  .ok [⟨leaf.id.val, request, nf canonNum proposition,
                    objects.map (·.metadata)⟩] := by
                simp [replayLeaf, hk, hr, run, hs, hg, if_pos he]
              rw [hval] at h
              injection h with hlist
              subst hlist
              exact .certified hk hr hs hg he
            · simp [replayLeaf, hk, hr, run, hs, hg, he] at h
    · have hj : judgments = [] := by
        cases hkind : leaf.kind <;> simp_all [replayLeaf]
      subst judgments
      exact .ordinary hk
  · intro h; cases h with
    | ordinary hk => cases hkind : leaf.kind <;> simp_all [replayLeaf]
    | certified hk hr hs hg he => simp [replayLeaf, hk, hr, run, hs, hg, he]

theorem replayLeaves_iff {snapshot registry leaves judgments} :
    replayLeaves snapshot registry leaves = .ok judgments ↔ AllReplayed snapshot registry leaves judgments := by
  induction leaves generalizing judgments with
  | nil => constructor
           · intro h; simp [replayLeaves] at h; subst judgments; constructor
           · intro h; cases h; rfl
  | cons leaf rest ih =>
    constructor
    · intro h
      cases hh : replayLeaf snapshot registry leaf with
      | error e => simp [replayLeaves, hh] at h
      | ok head =>
        cases ht : replayLeaves snapshot registry rest with
        | error e => simp [replayLeaves, hh, ht] at h
        | ok tail =>
          simp [replayLeaves, hh, ht] at h
          subst judgments
          exact .cons (replayLeaf_iff.mp hh) (ih.mp ht)
    · intro h; cases h with
      | cons hh ht => simp [replayLeaves, replayLeaf_iff.mpr hh, ih.mpr ht]

theorem admit_iff {snapshot policy manifest registry leaves judgments} :
    admit snapshot policy manifest registry leaves = .ok judgments ↔
      Admitted snapshot policy manifest registry leaves judgments := by
  constructor
  · intro h
    cases hb : firstInvalid (BindingValid policy manifest) leaves with
    | some leaf => simp [admit, bindingStage, hb] at h
    | none =>
      cases hc : firstInvalid (CapturedValid snapshot) (requestedManifest manifest leaves) with
      | some metadata => simp [admit, bindingStage, captureStage, hb, hc] at h
      | none =>
        exact ⟨(firstInvalid_none_iff _ _).mp hb, (firstInvalid_none_iff _ _).mp hc,
          replayLeaves_iff.mp (by simpa [admit, bindingStage, captureStage, hb, hc] using h)⟩
  · intro h
    have hb := (firstInvalid_none_iff _ _).mpr h.bindings
    have hc := (firstInvalid_none_iff _ _).mpr h.capture
    simpa [admit, bindingStage, captureStage, hb, hc] using replayLeaves_iff.mpr h.replay

theorem all_declared_supported {snapshot policy manifest registry leaves judgments}
    (h : Admitted snapshot policy manifest registry leaves judgments)
    {leaf : Leaf} (hl : leaf ∈ leaves) (hk : leaf.kind = .certified) :
    ∃ request, RequestBound policy manifest leaf request := by
  have hb := h.bindings leaf hl
  cases he : leaf.extraction with
  | none => simp [BindingValid, hk, he] at hb
  | some request => exact ⟨request, by simpa [BindingValid, hk, he] using hb⟩

theorem declared_replay_witness {snapshot registry leaves judgments}
    (h : AllReplayed snapshot registry leaves judgments) {leaf : Leaf}
    (hl : leaf ∈ leaves) (hk : leaf.kind = .certified) (he : leaf.extraction = some request) :
    ∃ judgment ∈ judgments, judgment.leaf = leaf.id.val ∧ judgment.request = request ∧
      ∃ objects proposition, supply snapshot (requestObjects request) = .ok objects ∧
        registry request objects = .ok proposition ∧
        nf canonNum proposition = nf canonNum leaf.prop ∧
        judgment.normalized = nf canonNum leaf.prop ∧
        judgment.dependencies = objects.map (·.metadata) := by
  induction h with
  | nil => simp at hl
  | @cons head rest hs ts hh ht ih =>
    rcases List.mem_cons.mp hl with rfl | hl
    · cases hh with
      | ordinary hn => exact False.elim (hn hk)
      | @certified rq objs prp lf hk' hr hsup hreg heq =>
        rw [he] at hr
        cases hr
        exact ⟨⟨leaf.id.val, request, nf canonNum prp, objs.map (·.metadata)⟩,
          List.mem_append_left (bs := ts) (by simp), rfl, rfl,
          objs, prp, hsup, hreg, heq, heq, rfl⟩
    · rcases ih hl with ⟨j, hj, hleaf, hr, hw⟩
      exact ⟨j, List.mem_append_right _ hj, hleaf, hr, hw⟩

theorem retained_supported {snapshot policy manifest registry leaves judgments}
    (h : Admitted snapshot policy manifest registry leaves judgments)
    (keep : Leaf → Bool) {leaf : Leaf} (hl : leaf ∈ leaves.filter keep)
    (hk : leaf.kind = .certified) :
    ∃ request, RequestBound policy manifest leaf request ∧
      ∃ judgment ∈ judgments, judgment.leaf = leaf.id.val ∧ judgment.request = request := by
  have hm := (List.mem_filter.mp hl).1
  rcases all_declared_supported h hm hk with ⟨request, hb⟩
  rcases declared_replay_witness h.replay hm hk hb.2.1 with ⟨j, hj, hid, hr, _⟩
  exact ⟨request, hb, j, hj, hid, hr⟩

theorem admission_deterministic {snapshot policy manifest registry leaves a b}
    (ha : admit snapshot policy manifest registry leaves = a)
    (hb : admit snapshot policy manifest registry leaves = b) : a = b := ha.symm.trans hb

theorem binding_precedes_capture {snapshot policy manifest registry leaves error}
    (h : bindingStage policy manifest leaves = some error) :
    admit snapshot policy manifest registry leaves = .error error := by simp [admit, h]
theorem capture_precedes_extraction {snapshot policy manifest registry leaves error}
    (hb : bindingStage policy manifest leaves = none)
    (hc : captureStage snapshot manifest leaves = some error) :
    admit snapshot policy manifest registry leaves = .error error := by simp [admit, hb, hc]

theorem firstInvalid_mem (p : α → Prop) [DecidablePred p] {xs : List α} {x : α}
    (h : firstInvalid p xs = some x) : x ∈ xs := by
  rcases firstInvalid_prefix p h with ⟨before, after, heq, _, _⟩
  rw [heq]; simp

theorem firstInvalid_congr (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (xs : List α) (h : ∀ x ∈ xs, p x ↔ q x) :
    firstInvalid p xs = firstInvalid q xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [firstInvalid]
    by_cases hp : p x
    · have hq := hx.mp hp; simp [hp, hq, ht]
    · have hq : ¬ q x := fun hq => hp (hx.mpr hq); simp [hp, hq]

theorem replayLeaf_registry_congr {snapshot first second leaf}
    (h : ∀ request, leaf.extraction = some request →
      run snapshot first request = run snapshot second request) :
    replayLeaf snapshot first leaf = replayLeaf snapshot second leaf := by
  unfold replayLeaf
  cases leaf.kind <;> cases he : leaf.extraction <;> simp_all

theorem replayLeaves_registry_congr {snapshot first second leaves}
    (h : ∀ leaf ∈ leaves, ∀ request, leaf.extraction = some request →
      run snapshot first request = run snapshot second request) :
    replayLeaves snapshot first leaves = replayLeaves snapshot second leaves := by
  induction leaves with
  | nil => rfl
  | cons leaf rest ih =>
    have hh := replayLeaf_registry_congr (h leaf List.mem_cons_self)
    have ht := ih (fun l hl => h l (List.mem_cons_of_mem _ hl))
    simp [replayLeaves, hh, ht]

theorem admission_registry_replacement {snapshot policy manifest first second leaves}
    (h : ∀ leaf ∈ leaves, ∀ request, leaf.extraction = some request →
      ∀ objects, supply snapshot (requestObjects request) = .ok objects →
        first request objects = second request objects) :
    admit snapshot policy manifest first leaves = admit snapshot policy manifest second leaves := by
  have hr := replayLeaves_registry_congr (fun leaf hl request he =>
    run_registry_replacement (h leaf hl request he))
  simp [admit, hr]

theorem request_local_of_source_local {s t leaves leaf request}
    (h : LocalOn (requestedIds leaves) s t) (hl : leaf ∈ leaves)
    (he : leaf.extraction = some request) : LocalOn (requestObjects request) s t := by
  intro id hi
  apply h id
  simp only [requestedIds, List.mem_flatMap]
  exact ⟨leaf, hl, by simp [he, hi]⟩

theorem replayLeaves_locality {s t registry leaves}
    (h : LocalOn (requestedIds leaves) s t) :
    replayLeaves s registry leaves = replayLeaves t registry leaves := by
  induction leaves with
  | nil => rfl
  | cons leaf rest ih =>
    have hh : replayLeaf s registry leaf = replayLeaf t registry leaf := by
      cases hk : leaf.kind <;> cases he : leaf.extraction <;> simp [replayLeaf, hk, he]
      · rw [run_locality (request_local_of_source_local h List.mem_cons_self he)]
    have ht : LocalOn (requestedIds rest) s t := by
      intro id hi
      apply h id
      simp only [requestedIds, List.flatMap_cons, List.mem_append] at hi ⊢
      exact Or.inr hi
    simp [replayLeaves, hh, ih ht]

theorem admission_locality {s t policy manifest registry leaves}
    (h : LocalOn (requestedIds leaves) s t) :
    admit s policy manifest registry leaves = admit t policy manifest registry leaves := by
  have hf : firstInvalid (CapturedValid s) (requestedManifest manifest leaves) =
      firstInvalid (CapturedValid t) (requestedManifest manifest leaves) := by
    apply firstInvalid_congr
    intro metadata hm
    have hi : metadata.id ∈ requestedIds leaves := by
      simpa using (List.mem_filter.mp hm).2
    simp [CapturedValid, h metadata.id hi]
  have hc : captureStage s manifest leaves = captureStage t manifest leaves := by
    unfold captureStage
    cases hs : firstInvalid (CapturedValid s) (requestedManifest manifest leaves) with
    | none => simp [← hf, hs]
    | some metadata =>
      have hi : metadata.id ∈ requestedIds leaves := by
        simpa using (List.mem_filter.mp (firstInvalid_mem _ hs)).2
      rw [← hf, hs]
      simp [h metadata.id hi]
  simp [admit, hc, replayLeaves_locality h]

theorem all_declared_certified_witness {snapshot policy manifest registry leaves judgments}
    (h : Admitted snapshot policy manifest registry leaves judgments)
    {leaf : Leaf} (hl : leaf ∈ leaves) (hk : leaf.kind = .certified) :
    ∃ request, RequestBound policy manifest leaf request ∧
      ∃ judgment ∈ judgments, judgment.leaf = leaf.id.val ∧ judgment.request = request ∧
        ∃ result, run snapshot registry request = .ok result ∧
          judgment.dependencies = result.dependencies ∧
          judgment.normalized = nf canonNum leaf.prop ∧
          nf canonNum result.proposition = nf canonNum leaf.prop ∧
          result.dependencies.map (·.id) = requestObjects request ∧
          ∀ metadata ∈ result.dependencies, ∃ id ∈ requestObjects request,
            ∃ object, lookup snapshot id = .ok object ∧ object.metadata = metadata := by
  rcases all_declared_supported h hl hk with ⟨request, hb⟩
  rcases declared_replay_witness h.replay hl hk hb.2.1 with
    ⟨judgment, hj, hid, hr, objects, proposition, hs, hg, heq, hn, hd⟩
  let result : RunResult := ⟨proposition, objects.map (·.metadata)⟩
  have hrun : run snapshot registry request = .ok result := by simp [run, hs, hg, result]
  exact ⟨request, hb, judgment, hj, hid, hr, result, hrun, hd, hn, heq,
    run_exact_declared_dependencies hrun, run_snapshot_membership hrun⟩

theorem retained_certified_witness {snapshot policy manifest registry leaves judgments}
    (h : Admitted snapshot policy manifest registry leaves judgments) (keep : Leaf → Bool)
    {leaf : Leaf} (hl : leaf ∈ leaves.filter keep) (hk : leaf.kind = .certified) :
    ∃ request, RequestBound policy manifest leaf request ∧
      ∃ judgment ∈ judgments, judgment.leaf = leaf.id.val ∧ judgment.request = request ∧
        ∃ result, run snapshot registry request = .ok result ∧
          judgment.normalized = nf canonNum leaf.prop := by
  rcases all_declared_certified_witness h (List.mem_filter.mp hl).1 hk with
    ⟨request, hb, judgment, hj, hid, hr, result, hrun, _, hn, _⟩
  exact ⟨request, hb, judgment, hj, hid, hr, result, hrun, hn⟩

theorem replayLeaves_first_error {snapshot registry leaves error}
    (h : replayLeaves snapshot registry leaves = .error error) :
    ∃ before leaf after, leaves = before ++ leaf :: after ∧
      (∀ earlier ∈ before, ∃ js, replayLeaf snapshot registry earlier = .ok js) ∧
      replayLeaf snapshot registry leaf = .error error := by
  induction leaves with
  | nil => simp [replayLeaves] at h
  | cons leaf rest ih =>
    cases hh : replayLeaf snapshot registry leaf with
    | error first =>
      have he : first = error := by simpa [replayLeaves, hh] using h
      subst first
      exact ⟨[], leaf, rest, rfl, by simp, hh⟩
    | ok js =>
      cases ht : replayLeaves snapshot registry rest with
      | ok tail => simp [replayLeaves, hh, ht] at h
      | error first =>
        have he : first = error := by simpa [replayLeaves, hh, ht] using h
        subst first
        rcases ih ht with ⟨before, failed, after, heq, hp, hf⟩
        refine ⟨leaf :: before, failed, after, by simp [heq], ?_, hf⟩
        intro earlier hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact ⟨js, hh⟩
        · exact hp earlier hm

theorem admission_first_extraction_error {snapshot policy manifest registry leaves error}
    (hb : bindingStage policy manifest leaves = none)
    (hc : captureStage snapshot manifest leaves = none)
    (h : admit snapshot policy manifest registry leaves = .error error) :
    ∃ before leaf after, leaves = before ++ leaf :: after ∧
      (∀ earlier ∈ before, ∃ js, replayLeaf snapshot registry earlier = .ok js) ∧
      replayLeaf snapshot registry leaf = .error error :=
  replayLeaves_first_error (by simpa [admit, hb, hc] using h)

theorem replay_checked_partition {snapshot policy manifest registry leaves judgments}
    (replayed : AllReplayed snapshot registry leaves judgments) :
    (∀ leaf ∈ leaves, BindingValid policy manifest leaf) →
    judgments.map (·.leaf) =
      (leaves.filter (fun leaf => leaf.kind == .certified)).map (·.id.val) := by
  induction replayed with
  | nil => intro _; rfl
  | @cons leaf rest head tail hh ht ih =>
    intro bindings
    have hbrest : ∀ l ∈ head, BindingValid policy manifest l :=
      fun l hl => bindings l (List.mem_cons_of_mem _ hl)
    cases hh with
    | ordinary hn =>
      simp [hn, ih hbrest]
    | certified hk he hs hg heq =>
      simp [hk, ih hbrest]

theorem checked_partition_exact {snapshot policy manifest registry leaves judgments}
    (h : Admitted snapshot policy manifest registry leaves judgments) :
    judgments.map (·.leaf) =
      (leaves.filter (fun leaf => leaf.kind == .certified)).map (·.id.val) :=
  replay_checked_partition h.replay h.bindings

theorem binding_stage_first_error {policy manifest leaves error}
    (h : bindingStage policy manifest leaves = some error) :
    ∃ before leaf after, leaves = before ++ leaf :: after ∧
      (∀ earlier ∈ before, BindingValid policy manifest earlier) ∧
      ¬ BindingValid policy manifest leaf ∧ error.stage = .binding ∧
      error.leaf = leaf.id.val := by
  unfold bindingStage at h
  cases hf : firstInvalid (BindingValid policy manifest) leaves with
  | none => simp [hf] at h
  | some leaf =>
    simp [hf] at h
    subst error
    rcases firstInvalid_prefix _ hf with ⟨before, after, heq, hvalid, hbad⟩
    exact ⟨before, leaf, after, heq, hvalid, hbad, rfl, rfl⟩

theorem capture_stage_first_error {snapshot manifest leaves error}
    (h : captureStage snapshot manifest leaves = some error) :
    ∃ before entry after, requestedManifest manifest leaves = before ++ entry :: after ∧
      (∀ earlier ∈ before, CapturedValid snapshot earlier) ∧
      ¬ CapturedValid snapshot entry ∧ error.stage = .capture ∧
      error.object = some entry.id ∧ error.leaf = firstReferencing leaves entry.id := by
  unfold captureStage at h
  cases hf : firstInvalid (CapturedValid snapshot) (requestedManifest manifest leaves) with
  | none => simp [hf] at h
  | some entry =>
    simp [hf] at h
    subst error
    rcases firstInvalid_prefix _ hf with ⟨before, after, heq, hvalid, hbad⟩
    exact ⟨before, entry, after, heq, hvalid, hbad, rfl, rfl, rfl⟩

end Lara.Evidence
