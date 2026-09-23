/- # Checked declaration registries
Frame bridge indices name checked declarations. Endpoints and maps are taken
from their elaboration witnesses. Relations, acceptance, canonicalizer equality,
and evidence-leaf/certificate obligations remain explicit host premises. -/
import Lara.PW.Surface

namespace Lara.PW.Surface.Declared

structure Host where
  K : Type
  ctx : K → Instance.Context
  ctxName : K → CtxId
  ctxOf : CtxId → Option K
  ctxOf_ctxName : ∀ k, ctxOf (ctxName k) = some k
  ctxName_of_ctxOf : ∀ n k, ctxOf n = some k → ctxName k = n
  canon_shared : ∀ k l, (ctx k).canon = (ctx l).canon

def Host.bridgeEnv (H : Host) (n : BridgeId) (s t : H.K) : BridgeEnv where
  name := n
  sourceName := H.ctxName s
  targetName := H.ctxName t
  source := H.ctx s
  target := H.ctx t
  canon_shared := H.canon_shared s t

/-- The original declaration together with its checked elaboration. -/
structure Resolved (H : Host) where
  decl : BridgeDecl
  source : H.K
  target : H.K
  out : Bridge
  checked : ElaboratesBridge (H.bridgeEnv decl.id source target) decl out

inductive LoadError where
  | duplicateBridge (name : BridgeId)
  | unknownSource (bridge : BridgeId) (context : CtxId)
  | unknownTarget (bridge : BridgeId) (context : CtxId)
  | invalidBridge (bridge : BridgeId) (fault : BridgeError)
deriving DecidableEq

/-- Resolve endpoints, then execute the existing bridge checker. -/
def resolve (H : Host) (d : BridgeDecl) : Except LoadError (Resolved H) :=
  match H.ctxOf d.source, H.ctxOf d.target with
  | none, _ => .error (.unknownSource d.id d.source)
  | _, none => .error (.unknownTarget d.id d.target)
  | some s, some t =>
    match h : elabBridge (H.bridgeEnv d.id s t) d with
    | .error e => .error (.invalidBridge d.id e)
    | .ok out => .ok ⟨d, s, t, out, elabBridge_sound _ _ _ h⟩

structure Registry (H : Host) where
  entries : List (Resolved H)

namespace Registry
variable {H : Host}

def lookup (E : Registry H) (n : BridgeId) : Option (Resolved H) :=
  E.entries.find? (fun r => r.decl.id == n)

theorem lookup_name (E : Registry H) {n : BridgeId} {r : Resolved H}
    (h : E.lookup n = some r) : r.decl.id = n := by
  have := List.find?_some h
  simpa using this

theorem lookup_mem (E : Registry H) {n : BridgeId} {r : Resolved H}
    (h : E.lookup n = some r) : r ∈ E.entries :=
  List.mem_of_find?_eq_some h

/-- Only names found in the checked registry can index a frame bridge. -/
def B (E : Registry H) := {n : BridgeId // (E.lookup n).isSome}

def get (E : Registry H) (b : E.B) : Resolved H :=
  (E.lookup b.val).get b.property

theorem lookup_get (E : Registry H) (b : E.B) :
    E.lookup b.val = some (E.get b) := by
  exact (Option.some_get _).symm

def bridgeOf (E : Registry H) (n : BridgeId) : Option E.B :=
  if h : (E.lookup n).isSome then some ⟨n, h⟩ else none

/-- Every entry's own name finds an entry, so it indexes a frame bridge. -/
theorem lookup_isSome_of_mem (E : Registry H) {r : Resolved H} (h : r ∈ E.entries) :
    (E.lookup r.decl.id).isSome := by
  unfold lookup
  exact List.find?_isSome.mpr ⟨r, h, by simp⟩

/-- The frame bridges named by the entries, in entry order. No lookup can fail. -/
def bridges (E : Registry H) : List E.B :=
  E.entries.attach.map fun r => ⟨r.val.decl.id, E.lookup_isSome_of_mem r.property⟩

/-- `bridges` names exactly the entries, in order; with `load_declarations`
this is the file's declaration order. -/
theorem bridges_names (E : Registry H) :
    E.bridges.map Subtype.val = E.entries.map (·.decl.id) := by
  rw [bridges]
  exact List.map_map.trans (List.attach_map_val (f := fun (r : Resolved H) => r.decl.id))

def data (E : Registry H)
    (R accept : (r : Resolved H) →
      Instance.World (H.ctx r.source) → Instance.World (H.ctx r.target) → Prop) :
    Sorted.SortedBridgeData where
  K := H.K
  ctx := H.ctx
  B := E.B
  bsrc := fun b => (E.get b).source
  btgt := fun b => (E.get b).target
  R := fun b => R (E.get b)
  accept := fun b => accept (E.get b)
  sym := fun b => (E.get b).out.sym

def naming (E : Registry H)
    (R accept : (r : Resolved H) →
      Instance.World (H.ctx r.source) → Instance.World (H.ctx r.target) → Prop) :
    Naming (E.data R accept) where
  ctxName := H.ctxName
  ctxOf := H.ctxOf
  ctxOf_ctxName := H.ctxOf_ctxName
  ctxName_of_ctxOf := H.ctxName_of_ctxOf
  bridgeName := Subtype.val
  bridgeOf := E.bridgeOf
  bridgeOf_bridgeName := by
    intro b
    simp only [bridgeOf, b.property, dif_pos]
    rfl
  bridgeName_of_bridgeOf := by
    intro n b h
    unfold bridgeOf at h
    split at h
    · cases h
      rfl
    · cases h

/-- Every frame bridge is exactly its checked declaration, at the declared
endpoints, with the declared symbol and evidence-leaf maps. -/
theorem coherent (E : Registry H)
    (R accept : (r : Resolved H) →
      Instance.World (H.ctx r.source) → Instance.World (H.ctx r.target) → Prop)
    (b : E.B) :
    (E.get b).decl.id = (E.naming R accept).bridgeName b ∧
    (E.get b).decl.source = H.ctxName ((E.data R accept).bsrc b) ∧
    (E.get b).decl.target = H.ctxName ((E.data R accept).btgt b) ∧
    ElaboratesBridge (H.bridgeEnv (E.get b).decl.id (E.get b).source
      (E.get b).target) (E.get b).decl (E.get b).out ∧
    (E.get b).out.sym = (E.data R accept).sym b ∧
    (E.data R accept).sym b = symMapOf (E.get b).decl.symbols ∧
    (E.get b).out.leafMap = leafMapOf (E.get b).decl.leaves :=
  ⟨E.lookup_name (E.lookup_get b), (E.get b).checked.source_eq,
    (E.get b).checked.target_eq, (E.get b).checked, rfl,
    (E.get b).checked.sym_eq, (E.get b).checked.leafMap_eq⟩

/-- A query-resolved name identifies that same checked declaration. -/
theorem resolved_decl (E : Registry H)
    (R accept : (r : Resolved H) →
      Instance.World (H.ctx r.source) → Instance.World (H.ctx r.target) → Prop)
    {n : BridgeId} {b : E.B}
    (h : (E.naming R accept).bridgeOf n = some b) :
    (E.get b).decl.id = n ∧ (E.get b) ∈ E.entries ∧
      (E.data R accept).sym b = symMapOf (E.get b).decl.symbols := by
  have hn := (E.naming R accept).bridgeName_of_bridgeOf n b h
  exact ⟨(E.coherent R accept b).1.trans hn,
    E.lookup_mem (E.lookup_get b), (E.get b).checked.sym_eq⟩
end Registry

/-- Process declarations in source order; duplicate identifiers are rejected.
Symbol and leaf entry order remains untouched by the existing checker. -/
def loadInto (H : Host) : Registry H → List BridgeDecl → Except LoadError (Registry H)
  | E, [] => .ok E
  | E, d :: ds =>
    if (E.lookup d.id).isSome then .error (.duplicateBridge d.id)
    else
      match resolve H d with
      | .error e => .error e
      | .ok r => loadInto H ⟨E.entries ++ [r]⟩ ds

def load (H : Host) (ds : List BridgeDecl) : Except LoadError (Registry H) :=
  loadInto H ⟨[]⟩ ds

/-- Resolving preserves the actual declaration, not merely its identifier. -/
theorem resolve_decl (H : Host) (d : BridgeDecl) (r : Resolved H)
    (h : resolve H d = .ok r) : r.decl = d := by
  unfold resolve at h
  split at h
  · cases h
  · cases h
  · split at h
    · cases h
    · cases h
      rfl

/-- Successful loading retains exactly the input declarations, in source order. -/
theorem loadInto_declarations (H : Host) (E : Registry H) (ds : List BridgeDecl)
    (E' : Registry H) (h : loadInto H E ds = .ok E') :
    E'.entries.map Resolved.decl = E.entries.map Resolved.decl ++ ds := by
  induction ds generalizing E with
  | nil =>
    cases h
    simp
  | cons d ds ih =>
    simp only [loadInto] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i r hr
        have hd := resolve_decl H d r hr
        have hh := ih _ h
        simpa [List.map_append, hd, List.append_assoc] using hh

theorem load_declarations (H : Host) (ds : List BridgeDecl) (E : Registry H)
    (h : load H ds = .ok E) : E.entries.map Resolved.decl = ds := by
  simpa using loadInto_declarations H ⟨[]⟩ ds E h

/-- Modal identifiers at every nesting depth, preserving occurrence order. -/
def modalNames : SForm → List BridgeId
  | .status _ _ | .top => []
  | .neg f => modalNames f
  | .conj f g => modalNames f ++ modalNames g
  | .box n f | .dia n f => n :: modalNames f

/-- Successful elaboration resolves every modal occurrence. -/
theorem elaborates_resolves {D : Sorted.SortedBridgeData} (E : Naming D)
    {k : D.frame.K} {f : SForm} {F : Form D.frame k}
    (h : Elaborates E f F) :
    ∀ n ∈ modalNames f, ∃ b, E.bridgeOf n = some b := by
  induction h with
  | status => simp [modalNames]
  | top => simp [modalNames]
  | neg _ ih => exact ih
  | conj _ _ ih ih' =>
    intro n hn
    cases List.mem_append.mp hn with
    | inl hn => exact ih n hn
    | inr hn => exact ih' n hn
  | box hb _ ih =>
    intro n hn
    cases List.mem_cons.mp hn with
    | inl hn => subst n; exact ⟨_, hb⟩
    | inr hn => exact ih n hn
  | dia hb _ ih =>
    intro n hn
    cases List.mem_cons.mp hn with
    | inl hn => subst n; exact ⟨_, hb⟩
    | inr hn => exact ih n hn

/-- All modal occurrences in an elaborated query use a declaration from the
loaded file, and use precisely that declaration's symbol map. -/
theorem elabForm_declared (H : Host) (ds : List BridgeDecl) (E : Registry H)
    (hload : load H ds = .ok E)
    (R accept : (r : Resolved H) →
      Instance.World (H.ctx r.source) → Instance.World (H.ctx r.target) → Prop)
    {k : (E.data R accept).frame.K} {f : SForm}
    {F : Form (E.data R accept).frame k}
    (h : elabForm (E.naming R accept) k f = .ok F) :
    ∀ n ∈ modalNames f, ∃ b : E.B,
      (E.naming R accept).bridgeOf n = some b ∧
      (E.get b).decl ∈ ds ∧ (E.get b).decl.id = n ∧
      (E.data R accept).sym b = symMapOf (E.get b).decl.symbols := by
  intro n hn
  obtain ⟨b, hb⟩ := elaborates_resolves (E.naming R accept)
    (elabForm_sound _ _ h) n hn
  obtain ⟨hid, hmem, hsym⟩ := E.resolved_decl R accept hb
  refine ⟨b, hb, ?_, hid, hsym⟩
  rw [← load_declarations H ds E hload]
  exact List.mem_map.mpr ⟨E.get b, hmem, rfl⟩

/-- The complete posed-query path has the same declaration provenance guarantee,
including modal occurrences nested below negation and conjunction. -/
theorem elabPosed_declared (H : Host) (ds : List BridgeDecl) (E : Registry H)
    (hload : load H ds = .ok E)
    (R accept : (r : Resolved H) →
      Instance.World (H.ctx r.source) → Instance.World (H.ctx r.target) → Prop)
    (p : Posed)
    (out : (k : (E.data R accept).frame.K) × Form (E.data R accept).frame k)
    (h : elabPosed (E.naming R accept) p = .ok out) :
    ∀ n ∈ modalNames p.form, ∃ b : E.B,
      (E.naming R accept).bridgeOf n = some b ∧
      (E.get b).decl ∈ ds ∧ (E.get b).decl.id = n ∧
      (E.data R accept).sym b = symMapOf (E.get b).decl.symbols := by
  cases hc : (E.naming R accept).ctxOf p.context with
  | none => simp [elabPosed, hc] at h
  | some k =>
    cases hf : elabForm (E.naming R accept) k p.form with
    | error e => simp [elabPosed, hc, hf] at h
    | ok F => exact elabForm_declared H ds E hload R accept hf

end Lara.PW.Surface.Declared
