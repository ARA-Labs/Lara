/-
# PW outer runtime: the finite executable reference

`pw-run 1` is the execution contract that the Haskell `lara pw` door and the
Lean `pw-run` executable both implement. A run file supplies the host that
`Lara.PW.Declared` leaves abstract: named worlds, each one checked by the
unchanged local checker, candidate edges with an explicit acceptance flag, and
source-claim comparisons. It embeds one `pw-surface 1` document verbatim, so
bridge declarations and posed queries use the `pw-surface 1` contract unchanged.

**What is proved here.**

* `decodeRun_encode` / `encodeRun_injective` — the structured codec round
  trip, as `Wire` proves it for the embedded document.
* `Model.evaluates_iff` — every printed query answer is `evalFinite` over a
  `Finite` presentation, hence `PW.Sat` of the elaborated formula in the frame
  the run declares (`evalFinite_iff`, `sat_congr`).
* `Model.compare_mem_iff_sat` — a comparison profile lists exactly the statuses
  `s` with `⟨b⟩Status_s(τ_b(c))`: the candidate list and acceptance test
  `Presents` the frame by construction, so `mem_compare_iff_sat_dia` applies.
* `Model.candidates_declared` / `Model.accepts_declared` — at a declared world
  the frame's candidates and acceptance are exactly the resolved edges, read at
  world positions. This rests on the loader's invariant that one context never
  holds two worlds with the same checked program (`LoadedCtx.distinct`).
* `resolveEdges_declared` / `loadWorlds_nodup` — resolution puts each declared
  edge along the bridge its name finds, with its declared acceptance, at the
  positions of the worlds it names; and no context holds two worlds with one
  identifier.
* `Model.candidates_named` / `Model.accepts_named`, and `load_candidates_named`
  / `load_accepts_named` for a model `loadModel` returns — together, the
  frame's candidates and acceptance are the file's declared edges read by name.
* `ResultTag.parse_text` / `ResultTag.text_injective` — every keyword of the
  result protocol has one spelling.
* `addWorld_quarantine_empty` / `addWorld_checks_declared` — a world the loader
  accepts has an empty §4.3 quarantine set, so the leaf table and argument list
  it checks are the declared ones. Consistent duplicate-report groups
  are inert; only a conflicting group is refused.

**The finite model boundary.** A context is inhabited by the worlds the file
declares and nothing else; a bridge's candidate relation is the finite edge
list; acceptance is the declared Boolean. `Sat` over an arbitrary frame is
proposition-valued and is not claimed executable. A world is a check-input
envelope accepted by `checkUnit`, so its statuses are the local checker's.
A world whose duplicate-report groups all agree is checked as declared; a
world with a conflicting group is refused, because §4.3 quarantine would make
a public status conditional, which a Boolean status atom cannot say.

**Sources.** A world's envelope is inline, or read from a file, or — the `lara`
form — elaborated from a `.lara` presentation program by the Haskell
runtime. This module has no surface parser, so the executable reports a `lara`
source as `world-input`; `lara pw-input` derives an equivalent run document
with every source inline, and that document is what the differential compares.

**What stays explicit.** Canonicalizer agreement holds because every context
uses the production `dcanon`. `leaf-ok` and `cert-ok` are parsed and required,
never proved; `rule-ok` is decided by the loader, exactly as in `Declared`.
-/
import Lara.PW.Declared
import Lara.PW.Finite
import Lara.PW.Wire
import Lara.Driver
import Lara.ListRel

namespace Lara.PW.Run

open Lara.Driver (Sx)
open Lara.Support
open Lara.PW.Instance
open Lara.PW.Surface Lara.PW.Surface.Declared
open Lara.Grounded (Status)

/-! ## 1. The run document -/

/-- A world identifier. Its own namespace: distinct from contexts and bridges. -/
structure WorldId where
  name : String
deriving DecidableEq

/-- The declared acceptance of one candidate edge. A closed sum, not a string. -/
inductive Acceptance where
  | accepted
  | rejected
deriving DecidableEq, Repr

def Acceptance.text : Acceptance → String
  | .accepted => "accepted"
  | .rejected => "rejected"

def Acceptance.isAccepted : Acceptance → Bool
  | .accepted => true
  | .rejected => false

/-- Where a world's check-input envelope comes from. `file` and `lara` paths
are resolved by the executable, relative to the run file's directory. A `lara`
path names a presentation program to elaborate; this reference has no surface
parser, so it can only report such a world as unreadable (`RunMain.readSource`).
-/
inductive WorldSource where
  | inline (input : Sx)
  | file (path : String)
  | lara (path : String)

structure WorldDecl where
  id : WorldId
  context : CtxId
  source : WorldSource

/-- One candidate edge of a bridge: `target` is a candidate of `source`. -/
structure EdgeDecl where
  bridge : BridgeId
  source : WorldId
  target : WorldId
  acceptance : Acceptance
deriving DecidableEq

/-- A source claim compared across one bridge at one source world. -/
structure CompareDecl where
  bridge : BridgeId
  world : WorldId
  claim : Atom
deriving DecidableEq

/-- The versioned unit of outer execution; every list keeps authored order. -/
structure RunDoc where
  worlds : List WorldDecl
  edges : List EdgeDecl
  comparisons : List CompareDecl
  document : Wire.Document

/-! ## 2. The `pw-run 1` codec -/

/-- The run grammar's own keywords. Nested forms reuse `Wire`'s vocabulary. -/
inductive Tag where
  | run | worlds | world | inline | file | lara | edges | edge | comparisons | compare
deriving DecidableEq, Repr

def Tag.text : Tag → String
  | .run => "pw-run"
  | .worlds => "worlds"
  | .world => "world"
  | .inline => "inline"
  | .file => "file"
  | .lara => "lara"
  | .edges => "edges"
  | .edge => "edge"
  | .comparisons => "comparisons"
  | .compare => "compare"

def Tag.parse (s : String) : Option Tag :=
  if s = Tag.text .run then some .run else
  if s = Tag.text .worlds then some .worlds else
  if s = Tag.text .world then some .world else
  if s = Tag.text .inline then some .inline else
  if s = Tag.text .file then some .file else
  if s = Tag.text .lara then some .lara else
  if s = Tag.text .edges then some .edges else
  if s = Tag.text .edge then some .edge else
  if s = Tag.text .comparisons then some .comparisons else
  if s = Tag.text .compare then some .compare else
  none

@[simp] theorem Tag.parse_text (t : Tag) : Tag.parse t.text = some t := by
  cases t <;> decide

theorem Tag.text_injective : Function.Injective Tag.text := by
  intro a b h
  have hp := congrArg Tag.parse h
  simpa using hp

/-- Version 1 is exact, as for `pw-surface`. -/
def version : String := "1"

private def malformed (what : String) : Except Wire.Error α :=
  .error ⟨.malformed, what⟩

def tagged (t : Tag) (args : List Sx) : Sx := .list (.atom t.text :: args)

def head (e : Sx) : Option (Tag × List Sx) :=
  match e with
  | .list (.atom s :: args) => (Tag.parse s).map (·, args)
  | _ => none

@[simp] theorem head_tagged (t : Tag) (args : List Sx) :
    head (tagged t args) = some (t, args) := by
  simp [head, tagged]

def sectionItems (t : Tag) (e : Sx) : Except Wire.Error (List Sx) :=
  match head e with
  | some (found, xs) => if found = t then .ok xs else malformed t.text
  | _ => malformed t.text

@[simp] theorem sectionItems_tagged (t : Tag) (xs : List Sx) :
    sectionItems t (tagged t xs) = .ok xs := by
  simp [sectionItems]

def encodeAcceptance (a : Acceptance) : Sx := .atom a.text

def decodeAcceptance : Sx → Except Wire.Error Acceptance
  | .atom s =>
    if s = Acceptance.text .accepted then .ok .accepted else
    if s = Acceptance.text .rejected then .ok .rejected else
    malformed "acceptance"
  | _ => malformed "acceptance"

@[simp] theorem decodeAcceptance_encode (a : Acceptance) :
    decodeAcceptance (encodeAcceptance a) = .ok a := by
  cases a <;> rfl

def encodeSource : WorldSource → Sx
  | .inline e => tagged .inline [e]
  | .file p => tagged .file [.atom p]
  | .lara p => tagged .lara [.atom p]

def decodeSource (e : Sx) : Except Wire.Error WorldSource :=
  match head e with
  | some (.inline, [x]) => .ok (.inline x)
  | some (.file, [.atom p]) => .ok (.file p)
  | some (.lara, [.atom p]) => .ok (.lara p)
  | _ => malformed "world-source"

@[simp] theorem decodeSource_encode (s : WorldSource) :
    decodeSource (encodeSource s) = .ok s := by
  cases s <;> simp [encodeSource, decodeSource]

def encodeWorld (d : WorldDecl) : Sx :=
  tagged .world [.atom d.id.name, .atom d.context.name, encodeSource d.source]

def decodeWorld (e : Sx) : Except Wire.Error WorldDecl :=
  match head e with
  | some (.world, [.atom w, .atom c, src]) => do
    let source ← decodeSource src
    pure ⟨⟨w⟩, ⟨c⟩, source⟩
  | _ => malformed "world"

@[simp] theorem decodeWorld_encode (d : WorldDecl) :
    decodeWorld (encodeWorld d) = .ok d := by
  simp [encodeWorld, decodeWorld]

def encodeEdge (d : EdgeDecl) : Sx :=
  tagged .edge [.atom d.bridge.name, .atom d.source.name, .atom d.target.name,
    encodeAcceptance d.acceptance]

def decodeEdge (e : Sx) : Except Wire.Error EdgeDecl :=
  match head e with
  | some (.edge, [.atom b, .atom s, .atom t, a]) => do
    let acceptance ← decodeAcceptance a
    pure ⟨⟨b⟩, ⟨s⟩, ⟨t⟩, acceptance⟩
  | _ => malformed "edge"

@[simp] theorem decodeEdge_encode (d : EdgeDecl) :
    decodeEdge (encodeEdge d) = .ok d := by
  simp [encodeEdge, decodeEdge]

def encodeCompare (d : CompareDecl) : Sx :=
  tagged .compare [.atom d.bridge.name, .atom d.world.name, Wire.encodeAtom d.claim]

def decodeCompare (e : Sx) : Except Wire.Error CompareDecl :=
  match head e with
  | some (.compare, [.atom b, .atom w, a]) => do
    let claim ← Wire.decodeAtom a
    pure ⟨⟨b⟩, ⟨w⟩, claim⟩
  | _ => malformed "comparison"

@[simp] theorem decodeCompare_encode (d : CompareDecl) :
    decodeCompare (encodeCompare d) = .ok d := by
  simp [encodeCompare, decodeCompare]

def encodeRun (d : RunDoc) : Sx :=
  tagged .run [.atom version, tagged .worlds (d.worlds.map encodeWorld),
    tagged .edges (d.edges.map encodeEdge),
    tagged .comparisons (d.comparisons.map encodeCompare),
    Wire.encodeDocument d.document]

/-- The version is read before the layout, so a later version reports
`unsupportedVersion` whatever sections it carries. Sections decode in order,
and each finishes before the next section header is read. -/
def decodeRun (e : Sx) : Except Wire.Error RunDoc :=
  match head e with
  | some (.run, .atom v :: rest) =>
    if v = version then
      match rest with
      | [ws, es, cs, doc] => do
        let worlds ← Wire.decodeList decodeWorld (← sectionItems .worlds ws)
        let edges ← Wire.decodeList decodeEdge (← sectionItems .edges es)
        let comparisons ← Wire.decodeList decodeCompare (← sectionItems .comparisons cs)
        let document ← Wire.decodeDocument doc
        pure ⟨worlds, edges, comparisons, document⟩
      | _ => malformed "run"
    else .error ⟨.unsupportedVersion, v⟩
  | _ => malformed "run"

/-- Full structured round trip, including the embedded surface document. -/
@[simp] theorem decodeRun_encode (d : RunDoc) : decodeRun (encodeRun d) = .ok d := by
  simp [encodeRun, decodeRun]

/-- Distinct run documents cannot share a token tree. -/
theorem encodeRun_injective : Function.Injective encodeRun := by
  intro a b h
  have hd := congrArg decodeRun h
  simp only [decodeRun_encode] at hd
  exact Except.ok.inj hd

/-- Read exactly one run document with the shared reader. -/
def parse (text : String) : Except Wire.Error RunDoc :=
  match Lara.Driver.parseWire text with
  | .error detail => .error ⟨.syntax, detail⟩
  | .ok e => decodeRun e

/-! ## 3. Worlds

A world is a check-input envelope accepted by the unchanged local checker. A
context's checking environment is the one its first world declares; every
later world of that context must declare the same one. -/

/-- The stable part of a check-input envelope: what a context shares. -/
structure Env where
  sigma : Lara.Sigma.Sigma
  policy : Lara.Policy.Policy
  leaves : List (LeafId × Atom)
  theories : List (Digest × List Atom)
deriving DecidableEq

/-- The PW context an environment denotes, under the production driver's
canonicalizer, leaf context and backend registry. -/
def Env.context (e : Env) : Context where
  canon := Lara.Driver.dcanon
  Gamma := Lara.Driver.buildGamma e.leaves
  CertOk := certOkOf (Lara.Driver.buildRegistry e.theories)
  sigma := e.sigma
  policy := e.policy

def envOf (d : Lara.Driver.Decoded) : Env := ⟨d.sigma, d.policy, d.leaves, d.theories⟩

/-- Run the unchanged checker on a world's program under its context. The
equations `World` demands come from `checkUnit_sound`, not from a new proof. -/
def checkWorld (e : Env) (ground : List Atom) (args : List SupportTerm)
    (atts : List Attack.Attack) : Except Lara.Check.Unit.UnitError (World e.context) :=
  match h : Lara.Check.Unit.checkUnit (Lara.Driver.buildGamma e.leaves)
      (Lara.Driver.buildRegistry e.theories) ground
      ({ sigma := e.sigma, policy := e.policy, args := args, atts := atts } : Lara.Unit) with
  | .error err => .error err
  | .ok u => .ok ⟨u, (Lara.Check.Unit.checkUnit_sound h).sigma_eq,
      (Lara.Check.Unit.checkUnit_sound h).policy_eq⟩

/-- A world's checked program: what identifies it within its context. -/
def stateOf {κ : Context} (w : World κ) : List SupportTerm × List Attack.Attack :=
  (w.unit.program.args, w.unit.program.atts)

structure LoadedWorld (e : Env) where
  id : WorldId
  world : World e.context

def LoadedWorld.state {e : Env} (w : LoadedWorld e) : List SupportTerm × List Attack.Attack :=
  stateOf w.world

/-- A context and its worlds, in declaration order. No two worlds share a
checked program, which is what lets a world value name its declaration. -/
structure LoadedCtx where
  name : CtxId
  env : Env
  worlds : List (LoadedWorld env)
  distinct : (worlds.map LoadedWorld.state).Nodup

/-- Why a declared world is refused. -/
inductive WorldError where
  /-- a second declaration of a world identifier -/
  | duplicateWorld (world : WorldId)
  /-- the world's source could not be read, parsed, or decoded as check-input -/
  | input (world : WorldId) (detail : String)
  /-- the envelope declares a duplicate-report group whose members disagree
  (§4.3): quarantine would fire, or the policy would escalate to R9 — either way
  the world is not an unconditionally checked unit. Names the first such group. -/
  | groups (world : WorldId) (group : String)
  /-- replay preflight or the local checker rejected the world -/
  | rejected (world : WorldId) (rejection : Lara.Driver.WireRejection)
  /-- the envelope's environment differs from its context's first world -/
  | environment (world : WorldId) (context : CtxId)
  /-- an earlier world of the same context has the same checked program -/
  | duplicateState (world earlier : WorldId)

/-- A world's source, already read and parsed by the executable. -/
structure WorldInput where
  id : WorldId
  context : CtxId
  input : Except String Sx

/-- Appending a fresh state keeps the states distinct. -/
theorem distinct_append {e : Env} {ws : List (LoadedWorld e)}
    (hws : (ws.map LoadedWorld.state).Nodup) (w : LoadedWorld e)
    (hnew : ∀ x ∈ ws, x.state ≠ w.state) :
    ((ws ++ [w]).map LoadedWorld.state).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨hws, by simp, ?_⟩
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
  subst hb
  exact hnew x hx

/-- Check one world under a context's environment and append it, refusing a
second world with an already declared checked program. -/
def extendCtx (c : LoadedCtx) (wid : WorldId) (ground : List Atom)
    (args : List SupportTerm) (atts : List Attack.Attack) :
    Except WorldError LoadedCtx :=
  match checkWorld c.env ground args atts with
  | .error err => .error (.rejected wid (Lara.Driver.rejectWire err))
  | .ok w =>
    match hfind : c.worlds.find? (fun x => decide (x.state = stateOf w)) with
    | some earlier => .error (.duplicateState wid earlier.id)
    | none =>
      .ok ⟨c.name, c.env, c.worlds ++ [⟨wid, w⟩], distinct_append c.distinct ⟨wid, w⟩
        (fun x hx heq => by
          have := List.find?_eq_none.mp hfind x hx
          simp only [decide_eq_true_eq] at this
          exact this heq)⟩

/-- Place a checked world in its named context, creating the context at the
end of the list when it is new. The environment check precedes checking. -/
def placeWorld (wid : WorldId) (cname : CtxId) (env : Env) (ground : List Atom)
    (args : List SupportTerm) (atts : List Attack.Attack) :
    List LoadedCtx → Except WorldError (List LoadedCtx)
  | [] => do
    let c ← extendCtx ⟨cname, env, [], List.nodup_nil⟩ wid ground args atts
    pure [c]
  | c :: cs =>
    if c.name = cname then
      if c.env = env then do
        let c' ← extendCtx c wid ground args atts
        pure (c' :: cs)
      else .error (.environment wid cname)
    else do
      let rest ← placeWorld wid cname env ground args atts cs
      pure (c :: rest)

/-- The first declared group whose members disagree, in declaration order. -/
def conflictingGroup (d : Lara.Driver.Decoded) : Option Groups.DupGroup :=
  d.groups.find? (fun g => ! Groups.consistentB Lara.Driver.dcanon d.leaves g)

/-- Load one world, mirroring the local driver's pipeline: decode, refuse a
conflicting duplicate-report group, replay preflight, then `checkUnit` over the
environment's leaves, theories and the envelope's queries as its ground atoms.

With no conflicting group the local driver's §4.3 quarantine is empty
(`Groups.quarantined_eq_nil`), so the leaf table and argument list handed to
`checkUnit` here are exactly the ones it would check
(`addWorld_checks_declared`). The attack list follows in fact — the local
driver's `keepAttack` filter only drops attacks whose arguments were
quarantined, and none were — but no theorem states that, so the citation
covers the two the theorem names and not attacks. -/
def addWorld (ctxs : List LoadedCtx) (seen : List WorldId) (wi : WorldInput) :
    Except WorldError (List LoadedCtx) := do
  if seen.contains wi.id then throw (.duplicateWorld wi.id)
  let e ← wi.input.mapError (.input wi.id)
  let ci ← (Lara.Driver.decodeCheckInput e).mapError (.input wi.id)
  let d := ci.decoded
  match conflictingGroup d with
  | some g => throw (.groups wi.id g.id)
  | none =>
  if (Lara.Driver.runtimeReplayFailure ci.replayId d.argIds d.args).isSome then
    throw (.rejected wi.id (.rejectClass .R13))
  let ground := d.leaves.map (·.2) ++ d.theories.flatMap (·.2) ++ d.queries
  placeWorld wi.id wi.context (envOf d) ground d.args d.atts ctxs

def loadWorlds : List LoadedCtx → List WorldId → List WorldInput →
    Except WorldError (List LoadedCtx)
  | ctxs, _, [] => .ok ctxs
  | ctxs, seen, wi :: rest => do
    let ctxs' ← addWorld ctxs seen wi
    loadWorlds ctxs' (seen ++ [wi.id]) rest

/-! ### World identifiers are unique within a context

`loadWorlds` refuses a repeated identifier before it checks anything, so no
context ever holds two worlds with one name. This is what lets an edge's
declared names determine world positions (`Model.candidates_named`). -/

private theorem bind_eq_ok {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

private theorem mapError_eq_ok {x : Except ε α} {g : ε → ε'} {a : α} :
    x.mapError g = .ok a ↔ x = .ok a := by
  cases x <;> simp [Except.mapError]

/-- The loader's naming invariant: no identifier repeats within a context, and
every loaded identifier has already been seen. -/
def IdsOk (ctxs : List LoadedCtx) (seen : List WorldId) : Prop :=
  ∀ c ∈ ctxs, (c.worlds.map (·.id)).Nodup ∧ ∀ x ∈ c.worlds, x.id ∈ seen

theorem IdsOk.mono {ctxs : List LoadedCtx} {seen : List WorldId} (h : IdsOk ctxs seen)
    (w : WorldId) : IdsOk ctxs (seen ++ [w]) := fun c hc =>
  ⟨(h c hc).1, fun x hx => List.mem_append_left _ ((h c hc).2 x hx)⟩

/-- Extending a context appends exactly the new identifier. -/
theorem extendCtx_ids {c c' : LoadedCtx} {wid : WorldId} {ground : List Atom}
    {args : List SupportTerm} {atts : List Attack.Attack}
    (h : extendCtx c wid ground args atts = .ok c') :
    c'.worlds.map (·.id) = c.worlds.map (·.id) ++ [wid] := by
  unfold extendCtx at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      simp

private theorem extendCtx_idsOk {c c' : LoadedCtx} {wid : WorldId} {ground : List Atom}
    {args : List SupportTerm} {atts : List Attack.Attack} {seen : List WorldId}
    (hc : (c.worlds.map (·.id)).Nodup ∧ ∀ x ∈ c.worlds, x.id ∈ seen) (hw : wid ∉ seen)
    (h : extendCtx c wid ground args atts = .ok c') :
    (c'.worlds.map (·.id)).Nodup ∧ ∀ x ∈ c'.worlds, x.id ∈ seen ++ [wid] := by
  have hids := extendCtx_ids h
  refine ⟨?_, fun x hx => ?_⟩
  · rw [hids, List.nodup_append]
    refine ⟨hc.1, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    intro hab
    subst hab
    obtain ⟨z, hz, hza⟩ := List.mem_map.mp ha
    exact hw (hza ▸ hc.2 z hz)
  · have hx' : x.id ∈ c'.worlds.map (·.id) := List.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hids, List.mem_append] at hx'
    rcases hx' with hx' | hx'
    · obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hx'
      exact List.mem_append_left _ (hzx ▸ hc.2 z hz)
    · exact List.mem_append_right _ hx'

/-- Placing a world whose identifier is unseen keeps the invariant. -/
theorem placeWorld_ids {wid : WorldId} {cname : CtxId} {env : Env} {ground : List Atom}
    {args : List SupportTerm} {atts : List Attack.Attack} {seen : List WorldId}
    (hw : wid ∉ seen) {ctxs ctxs' : List LoadedCtx} (hinv : IdsOk ctxs seen)
    (h : placeWorld wid cname env ground args atts ctxs = .ok ctxs') :
    IdsOk ctxs' (seen ++ [wid]) := by
  induction ctxs generalizing ctxs' with
  | nil =>
    simp only [placeWorld] at h
    obtain ⟨c, hc, h⟩ := bind_eq_ok.mp h
    cases h
    intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    refine extendCtx_idsOk ?_ hw hc
    exact ⟨List.nodup_nil, by simp⟩
  | cons c cs ih =>
    simp only [placeWorld] at h
    by_cases hn : c.name = cname
    · rw [if_pos hn] at h
      by_cases he : c.env = env
      · rw [if_pos he] at h
        obtain ⟨c', hc, h⟩ := bind_eq_ok.mp h
        cases h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact extendCtx_idsOk (hinv c List.mem_cons_self) hw hc
        · exact (hinv.mono wid) x (List.mem_cons_of_mem _ hx)
      · rw [if_neg he] at h
        cases h
    · rw [if_neg hn] at h
      obtain ⟨rest, hr, h⟩ := bind_eq_ok.mp h
      cases h
      have hrest := ih (fun c' hc' => hinv c' (List.mem_cons_of_mem _ hc')) hr
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (hinv.mono wid) x List.mem_cons_self
      · exact hrest x hx

/-- Loading one world keeps the invariant: `addWorld` refuses a seen identifier
before it places anything. -/
theorem addWorld_ids {ctxs ctxs' : List LoadedCtx} {seen : List WorldId} {wi : WorldInput}
    (hinv : IdsOk ctxs seen) (h : addWorld ctxs seen wi = .ok ctxs') :
    IdsOk ctxs' (seen ++ [wi.id]) := by
  unfold addWorld at h
  split at h
  · nomatch h
  · rename_i hc
    have hw : wi.id ∉ seen := fun hm => hc (List.contains_iff_mem.mpr hm)
    obtain ⟨e, -, h⟩ := bind_eq_ok.mp h
    obtain ⟨ci, -, h⟩ := bind_eq_ok.mp h
    simp only at h
    split at h
    · nomatch h
    · split at h
      · nomatch h
      · exact placeWorld_ids hw hinv h

theorem loadWorlds_ids {inputs : List WorldInput} :
    ∀ {ctxs ctxs' : List LoadedCtx} {seen : List WorldId}, IdsOk ctxs seen →
      loadWorlds ctxs seen inputs = .ok ctxs' → IdsOk ctxs' (seen ++ inputs.map (·.id)) := by
  induction inputs with
  | nil =>
    intro ctxs ctxs' seen hinv h
    simp only [loadWorlds] at h
    cases h
    simpa using hinv
  | cons wi rest ih =>
    intro ctxs ctxs' seen hinv h
    simp only [loadWorlds] at h
    obtain ⟨c1, h1, h2⟩ := bind_eq_ok.mp h
    have := ih (addWorld_ids hinv h1) h2
    simpa [List.append_assoc] using this

/-- **No context of a loaded run holds two worlds with one identifier.** -/
theorem loadWorlds_nodup {inputs : List WorldInput} {ctxs : List LoadedCtx}
    (h : loadWorlds [] [] inputs = .ok ctxs) :
    ∀ c ∈ ctxs, (c.worlds.map (·.id)).Nodup := fun c hc =>
  (loadWorlds_ids (fun _ hc => absurd hc List.not_mem_nil) h c hc).1

/-! ### Accepted worlds are unquarantined

The loader passes the decoded leaves, arguments and attacks to `checkUnit`
untouched, while the local driver first applies the §4.3 quarantine. The two
agree because the loader refuses every world with a conflicting group: for the
worlds it accepts, the quarantine set is empty, and quarantine is the identity.
-/

/-- The decoded envelope behind a world the loader accepted: it was read,
decoded, and none of its duplicate-report groups conflicts. -/
theorem addWorld_decoded {ctxs ctxs' : List LoadedCtx} {seen : List WorldId} {wi : WorldInput}
    (h : addWorld ctxs seen wi = .ok ctxs') :
    ∃ e ci, wi.input = .ok e ∧ Lara.Driver.decodeCheckInput e = .ok ci ∧
      ∀ g ∈ ci.decoded.groups, Groups.consistentB Lara.Driver.dcanon ci.decoded.leaves g = true := by
  unfold addWorld at h
  split at h
  · nomatch h
  · obtain ⟨e, he, h⟩ := bind_eq_ok.mp h
    obtain ⟨ci, hci, h⟩ := bind_eq_ok.mp h
    refine ⟨e, ci, mapError_eq_ok.mp he, mapError_eq_ok.mp hci, ?_⟩
    simp only at h
    split at h
    · nomatch h
    · rename_i hfind
      intro g hg
      have := List.find?_eq_none.mp hfind g hg
      simpa [conflictingGroup] using this

/-- **An accepted world's quarantine set is empty.** -/
theorem addWorld_quarantine_empty {ctxs ctxs' : List LoadedCtx} {seen : List WorldId}
    {wi : WorldInput} (h : addWorld ctxs seen wi = .ok ctxs') :
    ∃ e ci, wi.input = .ok e ∧ Lara.Driver.decodeCheckInput e = .ok ci ∧
      Groups.quarantined Lara.Driver.dcanon ci.decoded.leaves ci.decoded.groups = [] := by
  obtain ⟨e, ci, he, hci, hcons⟩ := addWorld_decoded h
  exact ⟨e, ci, he, hci, Groups.quarantined_eq_nil _ _ _ hcons⟩

/-- **The loader checks the declared unit.** For an accepted world, the local
driver's quarantined leaf table and argument list are the declared ones, so
`checkUnit` sees the same program under both drivers. -/
theorem addWorld_checks_declared {ctxs ctxs' : List LoadedCtx} {seen : List WorldId}
    {wi : WorldInput} (h : addWorld ctxs seen wi = .ok ctxs') :
    ∃ e ci, wi.input = .ok e ∧ Lara.Driver.decodeCheckInput e = .ok ci ∧
      Groups.quarantineLeaves
          (Groups.quarantined Lara.Driver.dcanon ci.decoded.leaves ci.decoded.groups)
          ci.decoded.leaves = ci.decoded.leaves ∧
      Groups.quarantineArgs
          (Groups.quarantined Lara.Driver.dcanon ci.decoded.leaves ci.decoded.groups)
          ci.decoded.argsRaw = ci.decoded.argsRaw := by
  obtain ⟨e, ci, he, hci, hq⟩ := addWorld_quarantine_empty h
  exact ⟨e, ci, he, hci, by rw [hq, Groups.quarantineLeaves_nil],
    by rw [hq, Groups.quarantineArgs_nil]⟩

/-! ## 4. The host a run declares -/

/-- The loaded contexts, in order of first declaration. -/
structure Hosted where
  ctxs : List LoadedCtx

namespace Hosted

def names (H : Hosted) : List CtxId := H.ctxs.map (·.name)

/-- Context indices are the declared names: no index can name a missing
context, and no uniqueness premise is needed to state the naming laws. -/
abbrev K (H : Hosted) : Type := {n : CtxId // n ∈ H.names}

theorem find_isSome (H : Hosted) (k : H.K) :
    (H.ctxs.find? (fun c => decide (c.name = k.val))).isSome := by
  obtain ⟨c, hc, hn⟩ := List.mem_map.mp k.property
  exact List.find?_isSome.mpr ⟨c, hc, by simp [hn]⟩

def entry (H : Hosted) (k : H.K) : LoadedCtx :=
  (H.ctxs.find? (fun c => decide (c.name = k.val))).get (H.find_isSome k)

theorem entry_mem (H : Hosted) (k : H.K) : H.entry k ∈ H.ctxs :=
  List.mem_of_find?_eq_some (Option.some_get (H.find_isSome k)).symm

def worldsAt (H : Hosted) (k : H.K) : List (LoadedWorld (H.entry k).env) :=
  (H.entry k).worlds

def host (H : Hosted) : Host where
  K := H.K
  ctx k := (H.entry k).env.context
  ctxName k := k.val
  ctxOf n := if h : n ∈ H.names then some ⟨n, h⟩ else none
  ctxOf_ctxName := by
    intro k
    simp only [dif_pos k.property]
  ctxName_of_ctxOf := by
    intro n k h
    by_cases hn : n ∈ H.names
    · rw [dif_pos hn] at h
      cases h
      rfl
    · rw [dif_neg hn] at h
      cases h
  canon_shared := fun _ _ => rfl

/-- The context declaring a world, if any. -/
def worldCtx? (H : Hosted) (w : WorldId) : Option CtxId :=
  (H.ctxs.find? (fun c => c.worlds.any (fun x => decide (x.id = w)))).map (·.name)

end Hosted

/-! ## 5. Edges and the declared frame -/

/-- A resolved edge: bridge name and world positions within their contexts. -/
structure REdge where
  bridge : BridgeId
  source : Nat
  target : Nat
  accepted : Bool
deriving DecidableEq

/-- Position of a checked program among a context's worlds. -/
def indexIn {e : Env} : List (LoadedWorld e) →
    List SupportTerm × List Attack.Attack → Nat → Option Nat
  | [], _, _ => none
  | x :: xs, s, n => if x.state = s then some n else indexIn xs s (n + 1)

/-- With distinct states, a declared world's program finds exactly its own
position. -/
theorem indexIn_declared {e : Env} :
    ∀ (ws : List (LoadedWorld e)), (ws.map LoadedWorld.state).Nodup →
      ∀ (i : Nat) (hi : i < ws.length) (n : Nat),
        indexIn ws (ws[i].state) n = some (n + i)
  | [], _, i, hi, _ => absurd hi (by simp)
  | x :: xs, hnd, i, hi, n => by
    have hx : x.state ∉ xs.map LoadedWorld.state := (List.nodup_cons.mp hnd).1
    have hxs : (xs.map LoadedWorld.state).Nodup := (List.nodup_cons.mp hnd).2
    cases i with
    | zero => simp [indexIn]
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      have hne : x.state ≠ xs[i].state := by
        intro heq
        exact hx (heq ▸ List.mem_map.mpr ⟨xs[i], List.getElem_mem hi', rfl⟩)
      simp only [indexIn, List.getElem_cons_succ, if_neg hne]
      rw [indexIn_declared xs hxs i hi' (n + 1)]
      congr 1
      omega

/-- A run's host, checked registry and resolved edges. -/
structure Model where
  H : Hosted
  E : Registry H.host
  edges : List REdge

namespace Model

variable (M : Model)

def index (k : M.H.K) (w : World (M.H.entry k).env.context) : Option Nat :=
  indexIn (M.H.worldsAt k) (stateOf w) 0

/-- The declared candidates of `w` along `r`, in edge declaration order. -/
def candidates (r : Resolved M.H.host) (w : World (M.H.host.ctx r.source)) :
    List (World (M.H.host.ctx r.target)) :=
  match M.index r.source w with
  | none => []
  | some i => M.edges.filterMap fun e =>
      if e.bridge = r.decl.id ∧ e.source = i then
        ((M.H.worldsAt r.target)[e.target]?).map (·.world)
      else none

/-- The declared acceptance of the edge from `w` to `v` along `r`. -/
def accepts (r : Resolved M.H.host) (w : World (M.H.host.ctx r.source))
    (v : World (M.H.host.ctx r.target)) : Bool :=
  match M.index r.source w, M.index r.target v with
  | some i, some j => M.edges.any fun e =>
      decide (e.bridge = r.decl.id) && decide (e.source = i) &&
        decide (e.target = j) && e.accepted
  | _, _ => false

def relation (r : Resolved M.H.host) (w : World (M.H.host.ctx r.source))
    (v : World (M.H.host.ctx r.target)) : Prop :=
  v ∈ M.candidates r w

def acceptance (r : Resolved M.H.host) (w : World (M.H.host.ctx r.source))
    (v : World (M.H.host.ctx r.target)) : Prop :=
  M.accepts r w v = true

def data : Sorted.SortedBridgeData := M.E.data M.relation M.acceptance

def naming : Naming M.data := M.E.naming M.relation M.acceptance

/-- The accepted successors, presented exactly (`mem_successors` holds by
`List.mem_filter`). -/
def finite : Finite M.data.frame where
  successors b w := (M.candidates (M.E.get b) w).filter (M.accepts (M.E.get b) w)
  mem_successors := by
    intro b w v
    exact List.mem_filter

def observation : Observation M.data.frame :=
  fun w c s => decide (cmpStatus w c.val = s)

/-- **Every printed query answer is satisfaction in the declared frame.** -/
theorem evaluates_iff {k : M.data.frame.K} (φ : Form M.data.frame k)
    (w : M.data.frame.World k) :
    evalFinite M.finite M.observation φ w = true ↔
      Sat M.data.frame (Sorted.cmpVal M.data) φ w := by
  apply (evalFinite_iff M.finite M.observation φ w).trans
  apply sat_congr
  intro k v c s
  change decide (cmpStatus v c.val = s) = true ↔ cmpStatus v c.val = s
  exact ⟨of_decide_eq_true, decide_eq_true⟩

/-- The source-claim comparison through the frame's declared symbol map, over
the declared candidates and acceptance. Not the reading of a modality. Stated
at the frame's own world and query types, so its theorems need no unfolding of
the host. -/
def compare (b : M.E.B) (w : M.data.frame.World (M.data.frame.src b))
    (claim : Atom) : Sorted.SortedResult :=
  Sorted.crossComparePosed (W := M.data.frame.World (M.data.frame.tgt b))
    (M.data.ctx (M.data.bsrc b)).sigma (M.data.ctx (M.data.btgt b)).sigma
    (M.data.sym b) claim (M.candidates (M.E.get b) w) (M.accepts (M.E.get b) w)
    (fun v q => cmpStatus v q.val)

/-- The comparison's inputs present the frame's bridge by construction. -/
theorem presents (b : M.E.B) (w : M.data.frame.World (M.data.frame.src b)) :
    Presents M.data.frame b w (M.candidates (M.E.get b) w)
      (M.accepts (M.E.get b) w) :=
  ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩

/-- **A comparison profile is the model's `⟨b⟩` reading.** When the claim
poses at the source and translates to a target query, a status occurs in the
printed profile exactly when `⟨b⟩Status_s(τ_b(c))` holds at the world. -/
theorem compare_mem_iff_sat (b : M.E.B)
    (w : M.data.frame.World (M.data.frame.src b)) (claim : Atom)
    (c : M.data.frame.Query (M.data.frame.src b))
    (d : M.data.frame.Query (M.data.frame.tgt b))
    (hpose : Sorted.pose (M.data.ctx (M.data.bsrc b)).sigma claim = .ok c)
    (htr : M.data.frame.translate b c = some d) (s : Status) :
    (∃ s₀ rest, M.compare b w claim = .compared (.comparable s₀ rest) ∧
        s ∈ s₀ :: rest) ↔
      @Sat M.data.frame (Sorted.cmpVal M.data) (M.data.frame.src b)
        (Form.dia (F := M.data.frame) b (.status s d)) w := by
  rw [← mem_compare_iff_sat_dia M.data.frame (Sorted.cmpVal M.data) b w c d
    (M.candidates (M.E.get b) w) (M.accepts (M.E.get b) w)
    (fun v q => cmpStatus v q.val) (fun _ _ _ => Iff.rfl) (M.presents b w) htr s, htr]
  have hcmp : M.compare b w claim = .compared
      (@crossCompare (M.data.frame.World (M.data.frame.tgt b)) _ (some d)
        (M.candidates (M.E.get b) w) (M.accepts (M.E.get b) w)
        (fun v q => cmpStatus v q.val)) :=
    Sorted.crossComparePosed_compared hpose htr
  rw [hcmp]
  constructor
  · rintro ⟨s₀, rest, h, hs⟩
    exact ⟨s₀, rest, Sorted.SortedResult.compared.inj h, hs⟩
  · rintro ⟨s₀, rest, h, hs⟩
    exact ⟨s₀, rest, congrArg Sorted.SortedResult.compared h, hs⟩

/-- A declared world finds its own position. -/
theorem index_declared (k : M.H.K) (i : Nat) (hi : i < (M.H.worldsAt k).length) :
    M.index k (M.H.worldsAt k)[i].world = some i := by
  have := indexIn_declared (M.H.worldsAt k) (M.H.entry k).distinct i hi 0
  simpa [index, LoadedWorld.state] using this

/-- **At a declared world the frame's candidates are the file's edges**, in
declaration order. -/
theorem candidates_declared (r : Resolved M.H.host) (i : Nat)
    (hi : i < (M.H.worldsAt r.source).length) :
    M.candidates r (M.H.worldsAt r.source)[i].world =
      M.edges.filterMap fun e =>
        if e.bridge = r.decl.id ∧ e.source = i then
          ((M.H.worldsAt r.target)[e.target]?).map (·.world)
        else none := by
  unfold candidates
  rw [M.index_declared r.source i hi]
  rfl

/-- **Between declared worlds the frame's acceptance is the declared flag.** -/
theorem accepts_declared (r : Resolved M.H.host) (i j : Nat)
    (hi : i < (M.H.worldsAt r.source).length)
    (hj : j < (M.H.worldsAt r.target).length) :
    M.accepts r (M.H.worldsAt r.source)[i].world (M.H.worldsAt r.target)[j].world =
      M.edges.any fun e =>
        decide (e.bridge = r.decl.id) && decide (e.source = i) &&
          decide (e.target = j) && e.accepted := by
  unfold accepts
  rw [M.index_declared r.source i hi, M.index_declared r.target j hj]

end Model

/-! ## 6. Resolution, execution, and the result protocol -/

/-- Why an edge cannot be placed in the declared frame. -/
inductive EdgeError where
  | unknownBridge (bridge : BridgeId)
  | unknownWorld (world : WorldId)
  | sourceContext (bridge : BridgeId) (world : WorldId)
  | targetContext (bridge : BridgeId) (world : WorldId)
  | duplicateEdge (bridge : BridgeId) (source target : WorldId)

/-- Why a comparison cannot be run. -/
inductive CompareError where
  | unknownBridge (bridge : BridgeId)
  | unknownWorld (world : WorldId)
  | sourceContext (bridge : BridgeId) (world : WorldId)

/-- The stage that refused a run. Incomparability is a result, never here. -/
inductive Error where
  | wire (fault : Wire.Error)
  | world (fault : WorldError)
  | bridge (fault : LoadError)
  | edge (fault : EdgeError)
  | query (fault : FormError)
  | comparison (fault : CompareError)
  | io (detail : String)
  | usage

/-- Position of a world, by name, among one context's worlds. -/
def positionIn {e : Env} (ws : List (LoadedWorld e)) (w : WorldId) : Option Nat :=
  ws.findIdx? (fun x => decide (x.id = w))

/-- Resolve one edge: the bridge, both worlds, both endpoint contexts, then
uniqueness of the (bridge, source, target) triple. -/
def resolveEdge (H : Hosted) (E : Registry H.host) (seen : List EdgeDecl)
    (d : EdgeDecl) : Except EdgeError REdge :=
  match E.lookup d.bridge with
  | none => .error (.unknownBridge d.bridge)
  | some r =>
    match H.worldCtx? d.source, H.worldCtx? d.target with
    | none, _ => .error (.unknownWorld d.source)
    | _, none => .error (.unknownWorld d.target)
    | some _, some _ =>
      match positionIn (H.worldsAt r.source) d.source,
          positionIn (H.worldsAt r.target) d.target with
      | none, _ => .error (.sourceContext d.bridge d.source)
      | _, none => .error (.targetContext d.bridge d.target)
      | some i, some j =>
        if seen.any (fun x => decide (x.bridge = d.bridge ∧ x.source = d.source ∧
            x.target = d.target)) then
          .error (.duplicateEdge d.bridge d.source d.target)
        else .ok ⟨d.bridge, i, j, d.acceptance.isAccepted⟩

def resolveEdges (H : Hosted) (E : Registry H.host) :
    List EdgeDecl → List EdgeDecl → Except EdgeError (List REdge)
  | _, [] => .ok []
  | seen, d :: ds => do
    let e ← resolveEdge H E seen d
    let rest ← resolveEdges H E (seen ++ [d]) ds
    pure (e :: rest)

/-! ### From declared names to frame positions

`candidates_declared` and `accepts_declared` read the frame off the resolved
edges, whose endpoints are positions. The results below close the remaining
step: resolution puts each declared edge at the positions of the worlds it
names, so the frame's candidates and acceptance are the file's edges read by
name (`Model.candidates_named`, `Model.accepts_named`, and `load_*` for a
loaded run). -/

theorem positionIn_some {e : Env} {ws : List (LoadedWorld e)} {w : WorldId} {i : Nat}
    (h : positionIn ws w = some i) : ∃ hi : i < ws.length, ws[i].id = w := by
  obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact ⟨hi, of_decide_eq_true hp⟩

/-- A resolved edge sits where its declaration says: along the bridge the
declared name finds, with the declared acceptance, at positions holding the
worlds with the declared source and target identifiers. -/
def EdgeAt (H : Hosted) (E : Registry H.host) (d : EdgeDecl) (e : REdge) : Prop :=
  ∃ r, E.lookup d.bridge = some r ∧ e.bridge = d.bridge ∧
    e.accepted = d.acceptance.isAccepted ∧
    (∃ h : e.source < (H.worldsAt r.source).length,
      (H.worldsAt r.source)[e.source].id = d.source) ∧
    (∃ h : e.target < (H.worldsAt r.target).length,
      (H.worldsAt r.target)[e.target].id = d.target)

theorem resolveEdge_declared {H : Hosted} {E : Registry H.host} {seen : List EdgeDecl}
    {d : EdgeDecl} {e : REdge} (h : resolveEdge H E seen d = .ok e) : EdgeAt H E d e := by
  unfold resolveEdge at h
  split at h
  · cases h
  · rename_i r hr
    split at h
    · cases h
    · cases h
    · split at h
      · cases h
      · cases h
      · rename_i i j hi hj
        split at h
        · cases h
        · cases h
          obtain ⟨hi', hiw⟩ := positionIn_some hi
          obtain ⟨hj', hjw⟩ := positionIn_some hj
          exact ⟨r, hr, rfl, rfl, ⟨hi', hiw⟩, ⟨hj', hjw⟩⟩

/-- **Resolution preserves the file's edges one for one**, in order. -/
theorem resolveEdges_declared {H : Hosted} {E : Registry H.host} {ds : List EdgeDecl} :
    ∀ {seen : List EdgeDecl} {es : List REdge},
      resolveEdges H E seen ds = .ok es → Lara.Forall₂ (EdgeAt H E) ds es := by
  induction ds with
  | nil =>
    intro seen es h
    simp only [resolveEdges] at h
    cases h
    exact .nil
  | cons d ds ih =>
    intro seen es h
    simp only [resolveEdges] at h
    obtain ⟨e, he, h⟩ := bind_eq_ok.mp h
    obtain ⟨rest, hr, h⟩ := bind_eq_ok.mp h
    cases h
    exact .cons (resolveEdge_declared he) (ih hr)

/-- With unique identifiers, a world's identifier determines its position. -/
theorem index_of_id {e : Env} {ws : List (LoadedWorld e)} (hnd : (ws.map (·.id)).Nodup)
    {i j : Nat} (hi : i < ws.length) (hj : j < ws.length) (h : ws[i].id = ws[j].id) :
    i = j :=
  (List.getElem_inj (i := i) (j := j) (h₀ := by simpa using hi) (h₁ := by simpa using hj)
    hnd).mp (by simpa using h)

/-- With unique identifiers, looking a world up by its identifier finds it. -/
theorem find?_id {e : Env} {ws : List (LoadedWorld e)} (hnd : (ws.map (·.id)).Nodup)
    {j : Nat} (hj : j < ws.length) :
    ws.find? (fun x => decide (x.id = ws[j].id)) = some ws[j] := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp, j, hj, rfl, fun k hk => ?_⟩
  have hne : ws[k].id ≠ ws[j].id := fun h => by
    have := index_of_id hnd (by omega) hj h
    omega
  simpa using hne

private theorem filterMap_congr_forall₂ {α β γ : Type} {R : α → β → Prop} {f : β → Option γ}
    {g : α → Option γ} (hfg : ∀ a b, R a b → f b = g a) :
    ∀ {as : List α} {bs : List β}, Lara.Forall₂ R as bs → bs.filterMap f = as.filterMap g
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    simp only [List.filterMap_cons, hfg _ _ h, filterMap_congr_forall₂ hfg hs]

private theorem any_congr_forall₂ {α β : Type} {R : α → β → Prop} {f : β → Bool} {g : α → Bool}
    (hfg : ∀ a b, R a b → f b = g a) :
    ∀ {as : List α} {bs : List β}, Lara.Forall₂ R as bs → bs.any f = as.any g
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    simp only [List.any_cons, hfg _ _ h, any_congr_forall₂ hfg hs]

namespace Model

variable (M : Model)

/-- A declared edge along the frame bridge `b` sits at `b`'s own endpoints. -/
private theorem edgeAt_get {b : M.E.B} {d : EdgeDecl} {e : REdge}
    (h : EdgeAt M.H M.E d e) (hb : d.bridge = b.val) :
    e.bridge = d.bridge ∧ e.accepted = d.acceptance.isAccepted ∧
    (∃ hs : e.source < (M.H.worldsAt (M.E.get b).source).length,
        (M.H.worldsAt (M.E.get b).source)[e.source].id = d.source) ∧
    (∃ ht : e.target < (M.H.worldsAt (M.E.get b).target).length,
        (M.H.worldsAt (M.E.get b).target)[e.target].id = d.target) := by
  obtain ⟨r, hr, hbr, hacc, hs, ht⟩ := h
  have hrb : r = M.E.get b := by
    rw [hb, M.E.lookup_get b] at hr
    exact (Option.some.inj hr).symm
  subst hrb
  exact ⟨hbr, hacc, hs, ht⟩

/-- **At a declared world the frame's candidates are the file's edges, read by
name**: the worlds the declared edges along `b` from that world's identifier
name as targets, in declaration order. `hres` and `hnd` are what `loadModel`
establishes (`loadModel_spec`). -/
theorem candidates_named {seen ds : List EdgeDecl}
    (hres : resolveEdges M.H M.E seen ds = .ok M.edges)
    (hnd : ∀ c ∈ M.H.ctxs, (c.worlds.map (·.id)).Nodup)
    (b : M.E.B) (i : Nat) (hi : i < (M.H.worldsAt (M.E.get b).source).length) :
    M.candidates (M.E.get b) (M.H.worldsAt (M.E.get b).source)[i].world =
      ds.filterMap fun d =>
        if d.bridge = b.val ∧ d.source = (M.H.worldsAt (M.E.get b).source)[i].id then
          ((M.H.worldsAt (M.E.get b).target).find?
            fun x => decide (x.id = d.target)).map (·.world)
        else none := by
  rw [M.candidates_declared (M.E.get b) i hi]
  have hname : (M.E.get b).decl.id = b.val := M.E.lookup_name (M.E.lookup_get b)
  have hS := hnd _ (M.H.entry_mem (M.E.get b).source)
  have hT := hnd _ (M.H.entry_mem (M.E.get b).target)
  refine filterMap_congr_forall₂ (fun d e h => ?_) (resolveEdges_declared hres)
  by_cases hb : d.bridge = b.val
  · obtain ⟨hbr, -, ⟨hs, hsid⟩, ⟨ht, htid⟩⟩ := M.edgeAt_get h hb
    have h1 : e.bridge = (M.E.get b).decl.id := by rw [hbr, hb, hname]
    have hiff : e.source = i ↔ d.source = (M.H.worldsAt (M.E.get b).source)[i].id := by
      constructor
      · rintro rfl
        exact hsid.symm
      · intro hd
        exact index_of_id hS hs hi (hsid.trans hd)
    by_cases hsrc : e.source = i
    · rw [if_pos ⟨h1, hsrc⟩, if_pos ⟨hb, hiff.mp hsrc⟩, ← htid,
        find?_id (ws := M.H.worldsAt (M.E.get b).target) hT ht, List.getElem?_eq_getElem ht]
    · rw [if_neg (fun hc => hsrc hc.2), if_neg (fun hc => hsrc (hiff.mpr hc.2))]
  · obtain ⟨_, _, hbr, _⟩ := h
    rw [if_neg (fun hc => hb (by rw [← hbr, hc.1, hname])), if_neg (fun hc => hb hc.1)]

/-- **Between declared worlds the frame's acceptance is the file's declared
flag, read by name**: some declared edge along `b` joins the two identifiers
and is declared `accepted`. -/
theorem accepts_named {seen ds : List EdgeDecl}
    (hres : resolveEdges M.H M.E seen ds = .ok M.edges)
    (hnd : ∀ c ∈ M.H.ctxs, (c.worlds.map (·.id)).Nodup)
    (b : M.E.B) (i j : Nat) (hi : i < (M.H.worldsAt (M.E.get b).source).length)
    (hj : j < (M.H.worldsAt (M.E.get b).target).length) :
    M.accepts (M.E.get b) (M.H.worldsAt (M.E.get b).source)[i].world
        (M.H.worldsAt (M.E.get b).target)[j].world =
      ds.any fun d =>
        decide (d.bridge = b.val) &&
          decide (d.source = (M.H.worldsAt (M.E.get b).source)[i].id) &&
          decide (d.target = (M.H.worldsAt (M.E.get b).target)[j].id) &&
          d.acceptance.isAccepted := by
  rw [M.accepts_declared (M.E.get b) i j hi hj]
  have hname : (M.E.get b).decl.id = b.val := M.E.lookup_name (M.E.lookup_get b)
  have hS := hnd _ (M.H.entry_mem (M.E.get b).source)
  have hT := hnd _ (M.H.entry_mem (M.E.get b).target)
  refine any_congr_forall₂ (fun d e h => ?_) (resolveEdges_declared hres)
  by_cases hb : d.bridge = b.val
  · obtain ⟨hbr, hacc, ⟨hs, hsid⟩, ⟨ht, htid⟩⟩ := M.edgeAt_get h hb
    have h1 : e.bridge = (M.E.get b).decl.id := by rw [hbr, hb, hname]
    have hsi : e.source = i ↔ d.source = (M.H.worldsAt (M.E.get b).source)[i].id :=
      ⟨fun h => h ▸ hsid.symm, fun hd => index_of_id hS hs hi (hsid.trans hd)⟩
    have htj : e.target = j ↔ d.target = (M.H.worldsAt (M.E.get b).target)[j].id :=
      ⟨fun h => h ▸ htid.symm, fun hd => index_of_id hT ht hj (htid.trans hd)⟩
    rw [decide_eq_true h1, decide_eq_true hb, decide_eq_decide.mpr hsi,
      decide_eq_decide.mpr htj, hacc]
  · obtain ⟨_, _, hbr, _⟩ := h
    have h1 : ¬ e.bridge = (M.E.get b).decl.id := fun hc => hb (by rw [← hbr, hc, hname])
    rw [decide_eq_false h1, decide_eq_false hb]
    rfl

end Model

/-- The first three stages of a run: worlds, bridges, then edges. -/
def loadModel (doc : RunDoc) (inputs : List WorldInput) : Except Error Model := do
  let ctxs ← (loadWorlds [] [] inputs).mapError Error.world
  let H : Hosted := ⟨ctxs⟩
  let E ← (load H.host doc.document.bridges).mapError Error.bridge
  let edges ← (resolveEdges H E [] doc.edges).mapError Error.edge
  pure ⟨H, E, edges⟩

/-- A loaded model's edges are the resolution of the file's edges, and no
context holds two worlds with one identifier. -/
theorem loadModel_spec {doc : RunDoc} {inputs : List WorldInput} {M : Model}
    (h : loadModel doc inputs = .ok M) :
    resolveEdges M.H M.E [] doc.edges = .ok M.edges ∧
      ∀ c ∈ M.H.ctxs, (c.worlds.map (·.id)).Nodup := by
  unfold loadModel at h
  obtain ⟨ctxs, h1, h⟩ := bind_eq_ok.mp h
  obtain ⟨E, -, h⟩ := bind_eq_ok.mp h
  obtain ⟨edges, h3, h⟩ := bind_eq_ok.mp h
  cases h
  exact ⟨mapError_eq_ok.mp h3, loadWorlds_nodup (mapError_eq_ok.mp h1)⟩

/-- **A loaded run's frame candidates are the file's edges, read by name.** -/
theorem load_candidates_named {doc : RunDoc} {inputs : List WorldInput} {M : Model}
    (h : loadModel doc inputs = .ok M) (b : M.E.B) (i : Nat)
    (hi : i < (M.H.worldsAt (M.E.get b).source).length) :
    M.candidates (M.E.get b) (M.H.worldsAt (M.E.get b).source)[i].world =
      doc.edges.filterMap fun d =>
        if d.bridge = b.val ∧ d.source = (M.H.worldsAt (M.E.get b).source)[i].id then
          ((M.H.worldsAt (M.E.get b).target).find?
            fun x => decide (x.id = d.target)).map (·.world)
        else none :=
  M.candidates_named (loadModel_spec h).1 (loadModel_spec h).2 b i hi

/-- **A loaded run's frame acceptance is the file's declared flag, read by
name.** -/
theorem load_accepts_named {doc : RunDoc} {inputs : List WorldInput} {M : Model}
    (h : loadModel doc inputs = .ok M) (b : M.E.B) (i j : Nat)
    (hi : i < (M.H.worldsAt (M.E.get b).source).length)
    (hj : j < (M.H.worldsAt (M.E.get b).target).length) :
    M.accepts (M.E.get b) (M.H.worldsAt (M.E.get b).source)[i].world
        (M.H.worldsAt (M.E.get b).target)[j].world =
      doc.edges.any fun d =>
        decide (d.bridge = b.val) &&
          decide (d.source = (M.H.worldsAt (M.E.get b).source)[i].id) &&
          decide (d.target = (M.H.worldsAt (M.E.get b).target)[j].id) &&
          d.acceptance.isAccepted :=
  M.accepts_named (loadModel_spec h).1 (loadModel_spec h).2 b i j hi hj

/-- Elaborate a posed query, then evaluate it at every world of its context,
in declaration order. -/
def runQuery (M : Model) (p : Posed) : Except FormError (List (WorldId × Bool)) := do
  let ⟨k, φ⟩ ← elabPosed M.naming p
  pure ((M.H.worldsAt k).map fun lw =>
    (lw.id, evalFinite M.finite M.observation φ lw.world))

/-- Resolve a comparison's bridge and source world, then compare. -/
def runCompare (M : Model) (d : CompareDecl) :
    Except CompareError Sorted.SortedResult :=
  match M.E.bridgeOf d.bridge with
  | none => .error (.unknownBridge d.bridge)
  | some b =>
    match M.H.worldCtx? d.world with
    | none => .error (.unknownWorld d.world)
    | some _ =>
      match (M.H.worldsAt (M.E.get b).source).find? (fun x => decide (x.id = d.world)) with
      | none => .error (.sourceContext d.bridge d.world)
      | some lw => .ok (M.compare b lw.world d.claim)

/-- A completed run: answers per query and world, and one result per
comparison, both in input order. -/
structure Outcome where
  queries : List (List (WorldId × Bool))
  comparisons : List (CompareDecl × Sorted.SortedResult)

/-- Stage order: worlds, bridges, edges, queries, comparisons. The first
refusal is the run's error; evaluation itself cannot fail. -/
def run (doc : RunDoc) (inputs : List WorldInput) : Except Error Outcome := do
  let M ← loadModel doc inputs
  let answers ← doc.document.queries.mapM fun p => (runQuery M p).mapError Error.query
  let results ← doc.comparisons.mapM fun d =>
    ((runCompare M d).map (d, ·)).mapError Error.comparison
  pure ⟨answers, results⟩

/-! ### The `pw-result 1` / `pw-error 1` protocol

Concrete spellings of the result protocol live only in `ResultTag.text`. -/

/-- Every keyword the `pw-result 1` / `pw-error 1` protocol prints, as a closed
sum with one spelling table (`ResultTag.text`). It is a separate closed sum
from the run grammar's `Tag` and from `Wire.Tag`, as `Lara.Map`'s verdict tags
are separate from the checker wire's. The output reuses a few input spellings
(`queries`, `comparisons`, `world`, `pred`, `con`) because it names the same
concepts, but it must not be able to perturb the input codec. A stage name and
a result node that share a spelling (`query`, `comparison`) share one
constructor, so every spelling still occurs once. The Haskell mirror is
`Lara.PW.Run.ResultTag`, without `usage` and the three bridge-name mismatches,
which cannot arise there. -/
inductive ResultTag where
  -- envelopes and stages
  | result | error | wire | world | bridge | edge | query | comparison | io | usage
  -- results
  | queries | atWorld | answerTrue | answerFalse | comparisons
  | comparable | incomparable | notPosable
  | translationUndefined | noCandidateWorld | allCandidateBridgesRejected
  | sourceQuery | targetQuery | bridgeVocabulary | pred | con
  | undeclaredPredicate | illSortedArguments
  -- faults
  | duplicateWorld | worldInput | worldGroups | worldRejected | contextEnvironment
  | duplicateWorldState
  | duplicateBridge | unknownSource | unknownTarget | invalidBridge
  | nameMismatch | sourceMismatch | targetMismatch | missingClause | ruleClauseFails
  | unknownBridge | unknownWorld | sourceContext | targetContext | duplicateEdge
  | unknownContext | bridgeSourceMismatch | notAQuery
deriving DecidableEq, Repr

/-- The printed spelling of a result keyword: the single source of truth. -/
def ResultTag.text : ResultTag → String
  | .result => "pw-result" | .error => "pw-error" | .wire => "wire"
  | .world => "world" | .bridge => "bridge" | .edge => "edge" | .query => "query"
  | .comparison => "comparison" | .io => "io" | .usage => "usage"
  | .queries => "queries" | .atWorld => "at" | .answerTrue => "true"
  | .answerFalse => "false" | .comparisons => "comparisons"
  | .comparable => "comparable" | .incomparable => "incomparable"
  | .notPosable => "not-posable"
  | .translationUndefined => "translation-undefined"
  | .noCandidateWorld => "no-candidate-world"
  | .allCandidateBridgesRejected => "all-candidate-bridges-rejected"
  | .sourceQuery => "source-query" | .targetQuery => "target-query"
  | .bridgeVocabulary => "bridge-vocabulary" | .pred => "pred" | .con => "con"
  | .undeclaredPredicate => "undeclared-predicate"
  | .illSortedArguments => "ill-sorted-arguments"
  | .duplicateWorld => "duplicate-world" | .worldInput => "world-input"
  | .worldGroups => "world-groups" | .worldRejected => "world-rejected"
  | .contextEnvironment => "context-environment"
  | .duplicateWorldState => "duplicate-world-state"
  | .duplicateBridge => "duplicate-bridge" | .unknownSource => "unknown-source"
  | .unknownTarget => "unknown-target" | .invalidBridge => "invalid-bridge"
  | .nameMismatch => "name-mismatch" | .sourceMismatch => "source-mismatch"
  | .targetMismatch => "target-mismatch" | .missingClause => "missing-clause"
  | .ruleClauseFails => "rule-clause-fails" | .unknownBridge => "unknown-bridge"
  | .unknownWorld => "unknown-world" | .sourceContext => "source-context"
  | .targetContext => "target-context" | .duplicateEdge => "duplicate-edge"
  | .unknownContext => "unknown-context"
  | .bridgeSourceMismatch => "bridge-source-mismatch" | .notAQuery => "not-a-query"

/-- Every result keyword, in declaration order. -/
def ResultTag.all : List ResultTag :=
  [.result, .error, .wire, .world, .bridge, .edge, .query, .comparison, .io, .usage,
    .queries, .atWorld, .answerTrue, .answerFalse, .comparisons,
    .comparable, .incomparable, .notPosable,
    .translationUndefined, .noCandidateWorld, .allCandidateBridgesRejected,
    .sourceQuery, .targetQuery, .bridgeVocabulary, .pred, .con,
    .undeclaredPredicate, .illSortedArguments,
    .duplicateWorld, .worldInput, .worldGroups, .worldRejected, .contextEnvironment,
    .duplicateWorldState,
    .duplicateBridge, .unknownSource, .unknownTarget, .invalidBridge,
    .nameMismatch, .sourceMismatch, .targetMismatch, .missingClause, .ruleClauseFails,
    .unknownBridge, .unknownWorld, .sourceContext, .targetContext, .duplicateEdge,
    .unknownContext, .bridgeSourceMismatch, .notAQuery]

/-- Read a result keyword back: the first tag with that spelling. -/
def ResultTag.parse (s : String) : Option ResultTag :=
  ResultTag.all.find? (fun t => t.text == s)

/-- Every keyword reads back as itself. Since `parse` returns the first match,
this also rules out two tags sharing a spelling. -/
@[simp] theorem ResultTag.parse_text (t : ResultTag) : ResultTag.parse t.text = some t := by
  cases t <;> decide

/-- No two result keywords share a spelling. -/
theorem ResultTag.text_injective : Function.Injective ResultTag.text := by
  intro a b h
  have hp := congrArg ResultTag.parse h
  simpa using hp

private def node (tag : ResultTag) (args : List Sx := []) : Sx :=
  .list (.atom tag.text :: args)

private def keyword (tag : ResultTag) : Sx := .atom tag.text

def encodeQueryFault : Sorted.QueryFault → Sx
  | .undeclaredPredicate p => node .undeclaredPredicate [.atom p.name]
  | .illSortedArguments p => node .illSortedArguments [.atom p.name]

def encodePosingFault : Sorted.PosingFault → Sx
  | .sourceQuery f => node .sourceQuery [encodeQueryFault f]
  | .targetQuery f => node .targetQuery [encodeQueryFault f]
  | .bridgeVocabulary f => node .bridgeVocabulary [match f with
      | .pred p => node .pred [.atom p.name]
      | .con c => node .con [.atom c.name]]

def encodeReason : IncomparabilityReason → Sx
  | .translationUndefined => keyword .translationUndefined
  | .noCandidateWorld => keyword .noCandidateWorld
  | .allCandidateBridgesRejected => keyword .allCandidateBridgesRejected

/-- Unposable claims, incomparable worlds, and status profiles stay apart. -/
def encodeComparison : Sorted.SortedResult → Sx
  | .notPosable f => node .notPosable [encodePosingFault f]
  | .compared (.incomparable r) => node .incomparable [encodeReason r]
  | .compared (.comparable s ss) => node .comparable ((s :: ss).map Wire.encodeStatus)

def encodeOutcome (o : Outcome) : Sx :=
  node .result [.atom version,
    node .queries (o.queries.map fun ws => node .query (ws.map fun wb =>
      node .atWorld [.atom wb.1.name, keyword (if wb.2 then .answerTrue else .answerFalse)])),
    node .comparisons (o.comparisons.map fun cr =>
      node .comparison [.atom cr.1.bridge.name, .atom cr.1.world.name,
        Wire.encodeAtom cr.1.claim, encodeComparison cr.2])]

def encodeBridgeFault : BridgeError → Sx
  | .nameMismatch a b => node .nameMismatch [.atom a.name, .atom b.name]
  | .sourceMismatch a b => node .sourceMismatch [.atom a.name, .atom b.name]
  | .targetMismatch a b => node .targetMismatch [.atom a.name, .atom b.name]
  | .missingClause c => node .missingClause [.atom c.text]
  | .ruleClauseFails => node .ruleClauseFails

def encodeWorldError : WorldError → Sx
  | .duplicateWorld w => node .duplicateWorld [.atom w.name]
  | .input w detail => node .worldInput [.atom w.name, .atom detail]
  | .groups w g => node .worldGroups [.atom w.name, .atom g]
  | .rejected w r => node .worldRejected
      [.atom w.name, .atom (Lara.Driver.wireRejectionString r)]
  | .environment w c => node .contextEnvironment [.atom w.name, .atom c.name]
  | .duplicateState w e => node .duplicateWorldState [.atom w.name, .atom e.name]

def encodeLoadError : LoadError → Sx
  | .duplicateBridge n => node .duplicateBridge [.atom n.name]
  | .unknownSource b n => node .unknownSource [.atom b.name, .atom n.name]
  | .unknownTarget b n => node .unknownTarget [.atom b.name, .atom n.name]
  | .invalidBridge b f => node .invalidBridge [.atom b.name, encodeBridgeFault f]

def encodeEdgeError : EdgeError → Sx
  | .unknownBridge b => node .unknownBridge [.atom b.name]
  | .unknownWorld w => node .unknownWorld [.atom w.name]
  | .sourceContext b w => node .sourceContext [.atom b.name, .atom w.name]
  | .targetContext b w => node .targetContext [.atom b.name, .atom w.name]
  | .duplicateEdge b s t => node .duplicateEdge [.atom b.name, .atom s.name, .atom t.name]

def encodeFormError : FormError → Sx
  | .unknownContext n => node .unknownContext [.atom n.name]
  | .unknownBridge n => node .unknownBridge [.atom n.name]
  | .bridgeSourceMismatch b a c =>
    node .bridgeSourceMismatch [.atom b.name, .atom a.name, .atom c.name]
  | .notAQuery n f => node .notAQuery [.atom n.name, encodeQueryFault f]

def encodeCompareError : CompareError → Sx
  | .unknownBridge b => node .unknownBridge [.atom b.name]
  | .unknownWorld w => node .unknownWorld [.atom w.name]
  | .sourceContext b w => node .sourceContext [.atom b.name, .atom w.name]

/-- Stable stage and fault constructors; only `syntax`, `world-input` and
`io` carry reader- or runtime-specific detail text. -/
def encodeError : Error → Sx
  | .wire e => envelope .wire [.atom e.tag.text, .atom e.detail]
  | .world e => envelope .world [encodeWorldError e]
  | .bridge e => envelope .bridge [encodeLoadError e]
  | .edge e => envelope .edge [encodeEdgeError e]
  | .query e => envelope .query [encodeFormError e]
  | .comparison e => envelope .comparison [encodeCompareError e]
  | .io detail => envelope .io [.atom detail]
  | .usage => envelope .usage [.atom "pw-run <file.sexp>"]
where
  envelope (stage : ResultTag) (args : List Sx) : Sx :=
    node .error (.atom version :: keyword stage :: args)

/-- Exit 2 for a run file that could not be read or decoded (and usage), 1 for
a run refused after decoding, 0 for a completed run. -/
def Error.exitCode : Error → UInt32
  | .wire _ | .io _ | .usage => 2
  | _ => 1

end Lara.PW.Run
