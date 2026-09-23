/-
PW0 — executable examples and the T7 witness.

Deliverables of the mechanization gate:

* the **T7 status non-preservation witness**: accepted source and target
  worlds in one context, an accepted bridge edge between them, and a checked
  support term present in both programs (the transported support), such that
  the source claim is `justified` and the target claim is `defeated` — the
  target adds one unattacked checked attacker. This fixes the boundary
  between exact support transport (T6, future) and status preservation (T8):
  transporting well-formed support does not transport grounded status. The
  full reading × valuation matrix is checked — `⟨b⟩` and `[b]`, each under
  the compiled valuation and (through T4, whose worked instances these are)
  under the source valuation.
* the **T2 negative controls**: frames on which each stronger frame axiom
  fails — T, D, B and 5 on a two-world frame, 4 on a three-world chain — so
  "normal, and no more" is a theorem rather than a doc comment. The first
  four depend on no axioms at all; `sat_4_fails` needs only `propext`.
* the **overlapping-fields example**: two contexts sharing the `p`/`q`
  vocabulary without either containing the other's — the second field declares
  `r`, which the first does not, and the first declares `s` (plus a sort and a
  constructor) that the second does not; the bridge translates the shared
  claim and the executable comparison returns a nonempty status profile.
* **one executable fixture per incomparability reason**, including the
  undefined translation for the source-only claim `s` — which the type
  prevents from ever being read as `gap` (gate 3), and `overlap_local_gap`
  pins the local status that the outer layer is refusing to report. The
  semantic half of gate 3 is instantiated too: `overlap_rejected_no_dia`
  discharges `not_sat_dia_of_incomparable` at a `Presents`-verified bridge.

Everything decidable is closed by `decide`; `native_decide` is banned by the
axiom audit (`ofReduceBool`). The facts that are not decidable propositions —
`t7_witness`, the four cells of the reading × valuation matrix, `presentsT7`,
`t7_dia_via_adequacy`, `t7_no_two_status`, `presentsOverlapRejected`,
`overlap_rejected_no_dia`, and the five frame-axiom refutations — are
ordinary term or tactic proofs. Measured: this module builds in under three
seconds, including three full `checkUnit` runs, so none of the fixtures need
splitting.

Two spellings are forced and worth stating once. `sigma_eq`/`policy_eq` are
closed by `rfl`, not `decide`: `Lara.Policy.Policy` has no `DecidableEq`
instance (nor does `Attack.DefeatPolicy`), so `decide` reports "failed to
synthesize"; `checkUnit` retains `sigma := unit.sigma` and
`policy := unit.policy` verbatim (`Check/Unit.lean:151`), so `rfl` closes
both. And index constructors are spelled `OneBridge.it` / `OneCtx.it` rather
than `.it` wherever the expected type is a `frame.B` / `frame.K` projection —
dotted notation resolves against the projection head, not through it.
-/

import Lara.Examples
import Lara.PW.Instance
import Lara.PW.Compare

namespace Lara.Examples.PW

open Lara.Support Lara.Compile Lara.Check Lara.Check.Unit
open Lara.PW Lara.PW.Instance
open Lara.Grounded (Status)

/-! ### The T7 context and its two worlds

One context: `sigmaEx`, and a policy whose defeat table declares `q` contrary
to `p` (directional — `firstMissingConflict?` checks `contraryMatchB dp source
target` in one direction only, so no reverse edge is demanded). The source
world admits only the `p` argument; the target admits the same `p` argument
*plus* one `q` attacker with the required typed undermine edge. Both units are
accepted by the unchanged `checkUnit`. -/

/-- `q` defeats `p`, directionally; no rules, so all arguments are leaves. -/
def polT7 : Policy.Policy :=
  { rules := [], defeat := ⟨[(apB, apA)], []⟩ }

/-- The shared scientific context of the T7 worlds. -/
def ctxT7 : Context :=
  { canon := id
  , Gamma := ΓEx
  , CertOk := certOkOf registryEx
  , sigma := sigmaEx
  , policy := polT7 }

/-- Source unit: the `p` argument alone. -/
def unitT7src : Lara.Unit :=
  { sigma := sigmaEx, policy := polT7, args := [.leaf l1], atts := [] }

def unitT7srcCheck := checkUnit ΓEx registryEx groundEx unitT7src

theorem unitT7src_accepted : unitT7srcCheck.isOk = true := by decide

def acceptedT7src : Lara.Unit.CheckedUnit id ΓEx (certOkOf registryEx) :=
  unitT7srcCheck.toOption.get (by decide)

/-- Target unit: the same `p` argument, plus one unattacked `q` attacker with
the typed undermine edge the contrary pair forces. `.undermine` (not
`.rebut`) because the target occurrence is a leaf. -/
def unitT7tgt : Lara.Unit :=
  { sigma := sigmaEx, policy := polT7
  , args := [.leaf l1, .leaf l2]
  , atts := [.undermine (.leaf l2) (.leaf l1) []] }

def unitT7tgtCheck := checkUnit ΓEx registryEx groundEx unitT7tgt

theorem unitT7tgt_accepted : unitT7tgtCheck.isOk = true := by decide

def acceptedT7tgt : Lara.Unit.CheckedUnit id ΓEx (certOkOf registryEx) :=
  unitT7tgtCheck.toOption.get (by decide)

/-- The source world. -/
def wT7src : World ctxT7 :=
  { unit := acceptedT7src, sigma_eq := rfl, policy_eq := rfl }

/-- The target world. -/
def wT7tgt : World ctxT7 :=
  { unit := acceptedT7tgt, sigma_eq := rfl, policy_eq := rfl }

/-- In the source world, `p` is justified. -/
theorem t7_src_justified : cmpStatus wT7src pA = Status.justified := by decide

/-- In the target world, the same claim is defeated: the added `q` attacker
is unattacked, hence grounded-`in`, and it attacks every complete support
argument of `p`. -/
theorem t7_tgt_defeated : cmpStatus wT7tgt pA = Status.defeated := by decide

/-- **The transported support term is a checked argument of the target.**
Stated exactly as proved: the term `leaf l1` is in the target program's
argument list. What makes it *the transported support* is
`t7_support_transported` below; this lemma is the membership half, kept
separate because `t7_witness` quotes it. -/
theorem t7_transport_wellFormed :
    SupportTerm.leaf l1 ∈ acceptedT7tgt.program.args := by decide

/-- **The transport really is the identity on the source claim's support.**
The membership above would be satisfied by any argument the target happens to
carry; this is the statement the T7/T8 boundary actually needs. The source and
target complete checked supports for `p` are the same nonempty index set
`[0]`, and — because support indices index the retained node cache — the
shared index resolves through *both* node caches to the same term `leaf l1`.
So the support `p` is justified by in the source is present, unchanged and
checked, in the target that defeats `p`. The minimal structural bridge PW0
needs before T6 exists. -/
theorem t7_support_transported :
    (claimAt wT7src pA).support = [0]
      ∧ (claimAt wT7tgt pA).support = [0]
      ∧ acceptedT7src.nodes[0]?.map (·.term) = some (SupportTerm.leaf l1)
      ∧ acceptedT7tgt.nodes[0]?.map (·.term) = some (SupportTerm.leaf l1) := by
  decide


/-! ### The T7 bridge and the packaged witness -/

/-- The T7 endobridge: one context, one bridge; the single candidate edge
relates exactly the two worlds above and is accepted; translation is the
identity where defined. -/
def bridgeT7 : BridgeData :=
  { K := OneCtx
  , ctx := fun _ => ctxT7
  , B := OneBridge
  , bsrc := fun _ => .it
  , btgt := fun _ => .it
  , R := fun _ w v => w = wT7src ∧ v = wT7tgt
  , accept := fun _ _ _ => True
  , translate := fun _ c => some c }

/-- **T7 — status non-preservation.** There is an accepted bridge edge whose
source world justifies the claim and whose target world defeats its (identity-)
translated form, while the transported support term remains a checked argument
of the target program. Status preservation therefore needs strictly more than
well-formed support transport — the boundary T8 will characterize. -/
theorem t7_witness :
    (bridgeT7.frame.A OneBridge.it wT7src wT7tgt) ∧
      cmpStatus wT7src pA = Status.justified ∧
      bridgeT7.translate OneBridge.it pA = some pA ∧
      cmpStatus wT7tgt pA = Status.defeated ∧
      SupportTerm.leaf l1 ∈ acceptedT7tgt.program.args :=
  ⟨⟨⟨rfl, rfl⟩, trivial⟩, t7_src_justified, rfl, t7_tgt_defeated,
    t7_transport_wellFormed⟩

/-- The same separation through the modal layer: at the source world,
`⟨b⟩Defeated(τ(p))` — the design's possible-status reading of the witness. -/
theorem t7_dia_defeated :
    Sat bridgeT7.frame (cmpVal bridgeT7)
      (.dia OneBridge.it (.status Status.defeated pA)) wT7src :=
  ⟨wT7tgt, ⟨⟨rfl, rfl⟩, trivial⟩, t7_tgt_defeated⟩
/-- The `[b]` reading as well: the only accepted successor defeats the claim,
so `[b]Defeated(τ(p))` holds too. Exercises the box clause at a real Lara
bridge rather than only in the generic T2 laws. -/
theorem t7_box_defeated :
    Sat bridgeT7.frame (cmpVal bridgeT7)
      (.box OneBridge.it (.status Status.defeated pA)) wT7src := by
  rintro v ⟨⟨_, rfl⟩, _⟩; exact t7_tgt_defeated

/-- **T4's worked instance.** The same witness under the *source* valuation,
obtained from the compiled one by `sat_src_iff_cmp` alone. A congruence
theorem with no instance can be true and useless; this is the instance. -/
theorem t7_dia_defeated_src :
    Sat bridgeT7.frame (srcVal bridgeT7)
      (.dia OneBridge.it (.status Status.defeated pA)) wT7src :=
  (sat_src_iff_cmp bridgeT7 wT7src
    (.dia OneBridge.it (.status Status.defeated pA))).mpr t7_dia_defeated

/-- The fourth cell of the reading × valuation matrix: the `[b]` witness under
the *source* valuation, again by `sat_src_iff_cmp` alone. With this the T7
separation is checked in both modal readings and under both valuations, with
no cell left to juxtaposition. -/
theorem t7_box_defeated_src :
    Sat bridgeT7.frame (srcVal bridgeT7)
      (.box OneBridge.it (.status Status.defeated pA)) wT7src :=
  (sat_src_iff_cmp bridgeT7 wT7src
    (.box OneBridge.it (.status Status.defeated pA))).mpr t7_box_defeated

/-- **The executable inputs really present the T7 bridge.** `Presents` is the
obligation `crossCompare` cannot state about itself: that the candidate list
enumerates `R_b(w, ·)` and the Bool test decides `accept_b(w, ·)`. Discharging
it once at a real Lara bridge is what keeps `mem_compare_iff_sat_dia` from
being an adequacy theorem with no instance. -/
theorem presentsT7 :
    Presents bridgeT7.frame OneBridge.it wT7src [wT7tgt] (fun _ => true) where
  mem_iff := by
    intro v
    constructor
    · intro hv; simp at hv; exact ⟨rfl, hv⟩
    · rintro ⟨_, rfl⟩; simp
  accept_iff := by intro v; exact ⟨fun _ => trivial, fun _ => rfl⟩

/-- **Adequacy, exercised.** The same `⟨b⟩Defeated(τ(p))` witness as
`t7_dia_defeated`, but obtained *through* the executable layer: run `crossCompare`
on the presented inputs, read `defeated` out of the profile, and cross to the
model by `mem_compare_iff_sat_dia`. This is the round trip the `Presents`
contract exists for — the executable comparison and the modal semantics
agreeing on one concrete bridge, rather than only in the abstract. -/
theorem t7_dia_via_adequacy :
    Sat bridgeT7.frame (cmpVal bridgeT7)
      (.dia OneBridge.it (.status Status.defeated pA)) wT7src :=
  (mem_compare_iff_sat_dia bridgeT7.frame (cmpVal bridgeT7) OneBridge.it
      wT7src pA pA [wT7tgt] (fun _ => true) (fun v q => cmpStatus v q)
      (fun _ _ _ => Iff.rfl) presentsT7 rfl Status.defeated).mp
    ⟨Status.defeated, [], by decide, by simp⟩

/-- **No Lara world reports two statuses for one claim**, at a real bridge:
`PW.not_sat_two_status` instantiated through `cmpVal_functional`. The generic
lemma needs a `Functional` valuation; this is the Lara discharge of that side
condition doing visible work. The explicit `@Sat … OneCtx.it` is the usual
index annotation — a world does not determine its context. -/
theorem t7_no_two_status :
    ¬ @Sat bridgeT7.frame (cmpVal bridgeT7) OneCtx.it
        (.conj (.status Status.justified pA) (.status Status.defeated pA))
        wT7src :=
  not_sat_two_status (cmpVal_functional bridgeT7) _ _ (by decide)


/-! ### Overlapping fields, and the three incomparability reasons

Two contexts sharing the `p`/`q` vocabulary, with **neither language
containing the other**: the second field declares `r`, which `sigmaEx` does
not, and `sigmaEx` declares `s` (plus the sort `Item` and the constructor `z`)
which the second field does not. So the shared fragment is a genuine
sub-vocabulary of both and of neither alone, and the bridge's translation
domain is exactly the shared claim. -/

/-- The second field's signature: `p` and `q` — the shared fragment — plus its
own `r`, and *not* `s`. The `r` declaration is what makes the two languages
genuinely overlapping rather than nested; nothing in the fixture uses it. -/
def sigmaOverlap : Lara.Sigma.Sigma :=
  { sorts := [], cons := []
  , preds := [⟨⟨"p"⟩, []⟩, ⟨⟨"q"⟩, []⟩, ⟨⟨"r"⟩, []⟩] }

def polOverlap : Policy.Policy := { rules := [], defeat := ⟨[], []⟩ }

def ctxOverlap : Context :=
  { canon := id
  , Gamma := ΓEx
  , CertOk := certOkOf registryEx
  , sigma := sigmaOverlap
  , policy := polOverlap }

/-- The second field's admitted state: one `q` argument. -/
def unitOverlap : Lara.Unit :=
  { sigma := sigmaOverlap, policy := polOverlap
  , args := [.leaf l2], atts := [] }

def unitOverlapCheck := checkUnit ΓEx registryEx [pA, pB] unitOverlap

theorem unitOverlap_accepted : unitOverlapCheck.isOk = true := by decide

def acceptedOverlap : Lara.Unit.CheckedUnit id ΓEx (certOkOf registryEx) :=
  unitOverlapCheck.toOption.get (by decide)

def wOverlap : World ctxOverlap :=
  { unit := acceptedOverlap, sigma_eq := rfl, policy_eq := rfl }

/-- The declared shared-fragment translation: defined at `q`, undefined
elsewhere — in particular at the `s` claim only the first field can state. -/
def tauOverlap : Atom → Option Atom :=
  fun c => if c = pB then some pB else none

/-- **The overlap comparison succeeds**: the shared claim translates, the one
candidate world is accepted, and the executable comparison returns the
nonempty profile of its status. -/
theorem overlap_comparable :
    crossCompare (tauOverlap pB) [wOverlap] (fun _ => true)
        (fun v q => cmpStatus v q) =
      .comparable Status.justified [] := by decide

/-- **The undefined translation is incomparable, not `gap`** (gate 3): the
`s` claim lies outside the bridge domain, and the tagged result names the
reason instead of any local status. -/
theorem overlap_translationUndefined :
    crossCompare (tauOverlap pC) [wOverlap] (fun _ => true)
        (fun v q => cmpStatus v q) =
      .incomparable .translationUndefined := by decide

/-- **What gate 3 is refusing to say.** The local layer *does* have an answer
for `s` at this world — `gap` — and it is the wrong answer to report across
the bridge, because here `gap` means "outside this field's vocabulary", not
"considered and unsupported". Without this fixture the previous theorem only
shows the outer layer says `translationUndefined`; with it, the two answers
are both pinned and visibly different. -/
theorem overlap_local_gap : cmpStatus wOverlap pC = Status.gap := by decide
/-- Reason 2 with an executable fixture: a defined translation and no
candidate world. -/
theorem overlap_noCandidate :
    crossCompare (tauOverlap pB) ([] : List (World ctxOverlap)) (fun _ => true)
        (fun v q => cmpStatus v q) = .incomparable .noCandidateWorld := by decide

/-- Reason 3 with an executable fixture: candidates exist, none accepted. All
three incomparability reasons now have both a theorem and a fixture. -/
theorem overlap_allRejected :
    crossCompare (tauOverlap pB) [wOverlap] (fun _ => false)
        (fun v q => cmpStatus v q)
      = .incomparable .allCandidateBridgesRejected := by decide

/-- The overlap endobridge with every candidate bridge rejected: the same
translation and candidate as `overlap_allRejected`, packaged as `BridgeData`
so the *semantic* half of gate 3 can be exercised at it. -/
def bridgeOverlapRejected : BridgeData :=
  { K := OneCtx
  , ctx := fun _ => ctxOverlap
  , B := OneBridge
  , bsrc := fun _ => .it
  , btgt := fun _ => .it
  , R := fun _ _ v => v = wOverlap
  , accept := fun _ _ _ => False
  , translate := fun _ => tauOverlap }

/-- The executable inputs of `overlap_allRejected` present that bridge: the
one-element candidate list enumerates `R`, and the constantly-false test
decides the constantly-false acceptance. -/
theorem presentsOverlapRejected :
    Presents bridgeOverlapRejected.frame OneBridge.it wOverlap [wOverlap]
      (fun _ => false) where
  mem_iff := by
    intro v
    constructor
    · intro hv; simp at hv; exact hv
    · rintro rfl; simp
  accept_iff := by
    intro v
    constructor
    · intro h; exact absurd h (by decide)
    · intro h; exact (show False from h).elim

/-- **Gate 3's semantic half, exercised.** `not_sat_dia_of_incomparable` at
the rejected overlap bridge: the translation is defined and the executable
result is incomparable, so the model satisfies `⟨b⟩Status_s(q)` for *no*
status `s` — the condition no local status could report, discharged at a
concrete `Presents` instance rather than only in the abstract. The sibling
instantiation for `mem_compare_iff_sat_dia` is `t7_dia_via_adequacy`. -/
theorem overlap_rejected_no_dia (s : Status) :
    ¬ Sat bridgeOverlapRejected.frame (cmpVal bridgeOverlapRejected)
        (.dia OneBridge.it (.status s pB)) wOverlap :=
  not_sat_dia_of_incomparable bridgeOverlapRejected.frame
    (cmpVal bridgeOverlapRejected) OneBridge.it wOverlap pB pB [wOverlap]
    (fun _ => false) (fun v q => cmpStatus v q) presentsOverlapRejected
    (show tauOverlap pB = some pB by decide)
    (r := .allCandidateBridgesRejected)
    (show crossCompare (tauOverlap pB) [wOverlap] (fun _ => false)
        (fun v q => cmpStatus v q)
      = .incomparable .allCandidateBridgesRejected by decide) s


/-! ### T2 negative controls — normal, and no more

The T2 block proves K, necessitation, duality, `[b]⊤` and `[b]∧`. It also
claims no *stronger* frame axiom holds. That half is mechanized here rather
than asserted, for every axiom the T2 docstring names: on a two-world frame
whose only accepted edge runs `true → false`, with a valuation true exactly
at `false`, axioms T (`sat_T_fails`), D (`sat_D_fails`), B (`sat_B_fails`)
and 5 (`sat_5_fails`) all fail; axiom 4 holds vacuously on that frame, so
`sat_4_fails` refutes it on a three-world chain `0 → 1 → 2` with no composite
edge. The repo mechanizes its refutations elsewhere
(`selfEdgeCode_not_realizable`, `unrangedEx_not_invariant`); this is the same
discipline. -/

/-- A frame with one accepted edge `true → false` and nothing else. -/
def frameT : Lara.PW.Frame where
  K := OneCtx
  B := OneBridge
  src := fun _ => .it
  tgt := fun _ => .it
  World := fun _ => Bool
  Query := fun _ => Bool
  R := fun _ w v => w = true ∧ v = false
  accept := fun _ _ _ => True
  translate := fun _ => some

/-- True exactly at the target world. -/
def valT : Lara.PW.Valuation frameT := fun {_} w _ _ => w = false

/-- **The reflexivity axiom T fails.** So PW0's logic is normal and no more —
a theorem, not a comment. Depends on no axioms. -/
theorem sat_T_fails :
    ¬ (∀ (w : Bool) (φ : Lara.PW.Form frameT OneCtx.it),
        Lara.PW.Sat frameT valT (.box OneBridge.it φ) w → Lara.PW.Sat frameT valT φ w) := by
  intro h
  have hbox : Lara.PW.Sat frameT valT (.box OneBridge.it (.status Status.gap true)) true := by
    rintro v ⟨⟨_, rfl⟩, _⟩
    rfl
  have hbad : (true : Bool) = false := h true _ hbox
  exact absurd hbad (by decide)

/-- **The seriality axiom D fails** on the same frame: at world `false` there
is no accepted successor, so `[b]φ` holds vacuously while `⟨b⟩φ` has no
witness. Depends on no axioms. -/
theorem sat_D_fails :
    ¬ (∀ (w : Bool) (φ : Lara.PW.Form frameT OneCtx.it),
        Lara.PW.Sat frameT valT (.box OneBridge.it φ) w →
          Lara.PW.Sat frameT valT (.dia OneBridge.it φ) w) := by
  intro h
  have hbox : Lara.PW.Sat frameT valT
      (.box OneBridge.it (.status Status.gap true)) false := by
    rintro v ⟨⟨hw, _⟩, _⟩
    exact absurd hw (by decide)
  obtain ⟨v, ⟨⟨hw, _⟩, _⟩, _⟩ := h false _ hbox
  exact absurd hw (by decide)

/-- **The symmetry axiom B fails** on the same frame: `φ` holds at `true`,
but the only successor `false` has no successor of its own, so `[b]⟨b⟩φ`
fails. Depends on no axioms. -/
theorem sat_B_fails :
    ¬ (∀ (w : Bool) (φ : Lara.PW.Form frameT OneCtx.it),
        Lara.PW.Sat frameT valT φ w →
          Lara.PW.Sat frameT valT
            (.box OneBridge.it (.dia OneBridge.it φ)) w) := by
  intro h
  have hφ : Lara.PW.Sat frameT valT
      (.neg (.status Status.gap true) : Lara.PW.Form frameT OneCtx.it) true := by
    intro hcontra
    exact absurd (show (true : Bool) = false from hcontra) (by decide)
  obtain ⟨u, ⟨⟨hw, _⟩, _⟩, _⟩ := h true _ hφ false ⟨⟨rfl, rfl⟩, trivial⟩
  exact absurd hw (by decide)

/-- **The Euclidean axiom 5 fails** on the same frame: `⟨b⟩φ` holds at `true`
with witness `false`, but at that same successor `⟨b⟩φ` fails, so `[b]⟨b⟩φ`
does too. Depends on no axioms. -/
theorem sat_5_fails :
    ¬ (∀ (w : Bool) (φ : Lara.PW.Form frameT OneCtx.it),
        Lara.PW.Sat frameT valT (.dia OneBridge.it φ) w →
          Lara.PW.Sat frameT valT
            (.box OneBridge.it (.dia OneBridge.it φ)) w) := by
  intro h
  have hdia : Lara.PW.Sat frameT valT
      (.dia OneBridge.it (.status Status.gap true)) true :=
    ⟨false, ⟨⟨rfl, rfl⟩, trivial⟩, rfl⟩
  obtain ⟨u, ⟨⟨hw, _⟩, _⟩, _⟩ := h true _ hdia false ⟨⟨rfl, rfl⟩, trivial⟩
  exact absurd hw (by decide)

/-- A three-world chain `0 → 1 → 2` with no composite edge. `frameT` cannot
refute transitivity — with a single edge, `[b][b]φ` is vacuous everywhere —
so axiom 4 gets the minimal frame on which it has content. -/
def frame4 : Lara.PW.Frame where
  K := OneCtx
  B := OneBridge
  src := fun _ => .it
  tgt := fun _ => .it
  World := fun _ => Fin 3
  Query := fun _ => Bool
  R := fun _ w v => (w = 0 ∧ v = 1) ∨ (w = 1 ∧ v = 2)
  accept := fun _ _ _ => True
  translate := fun _ => some

/-- True everywhere except the end of the chain. -/
def val4 : Lara.PW.Valuation frame4 := fun {_} w _ _ => w ≠ (2 : Fin 3)

/-- **The transitivity axiom 4 fails** on the chain: `[b]φ` holds at `0`
(its one successor `1` satisfies `φ`), but `[b][b]φ` reaches `2`, where `φ`
fails. Needs only `propext` (the audit records the other four refutations as
axiom-free). -/
theorem sat_4_fails :
    ¬ (∀ (w : Fin 3) (φ : Lara.PW.Form frame4 OneCtx.it),
        Lara.PW.Sat frame4 val4 (.box OneBridge.it φ) w →
          Lara.PW.Sat frame4 val4 (.box OneBridge.it (.box OneBridge.it φ)) w) := by
  intro h
  have hbox : Lara.PW.Sat frame4 val4
      (.box OneBridge.it (.status Status.gap true)) (0 : Fin 3) := by
    rintro v ⟨hR, _⟩
    rcases hR with ⟨_, rfl⟩ | ⟨h01, _⟩
    · exact (by decide : (1 : Fin 3) ≠ 2)
    · exact absurd h01 (by decide)
  have hbad : (2 : Fin 3) ≠ 2 :=
    h 0 (.status Status.gap true) hbox (1 : Fin 3)
      ⟨Or.inl ⟨rfl, rfl⟩, trivial⟩ (2 : Fin 3) ⟨Or.inr ⟨rfl, rfl⟩, trivial⟩
  exact absurd hbad (by decide)

end Lara.Examples.PW
