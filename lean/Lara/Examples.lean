/-
Concrete conformance examples (`Lara.Examples`) — constructed programs that
pin the executable behavior of the frozen §6.1/§7.1/§8 definitions, so a
mistranscription of `openMandatory`, `subterm`, or the closure-edge relation
cannot hide behind headline theorems that only quantify abstractly.

What is exercised, per the review findings on the M1 lock pass:

* **§6.1 obligation accounting** — `mixed_holes_obligations`: an instance
  with one open mandatory and one open optional question yields exactly the
  mandatory obligation (`O = [q1]`, the optional hole is a diagnostic);
  `nested_obligation_propagates`: a premise subterm's open obligation flows
  into the parent's `O`; `discharge_obligation_propagates`: the same holds
  for a discharge subterm; `repeated_obligation_deduplicated`: two children
  reporting the same question still yield the singleton obligation set;
  `missing_question_rejected`: a declared question in
  neither the discharge map nor the hole set makes the instance untypable;
  `overlapping_question_rejected`: a question cannot be both discharged and
  open (the `D ⊎ H` cover/disjointness doing its job).
* **§7.1 position lookup** — `subterm_boundaries`: nested `.prem`/`.ques`
  traversal including a mixed path, and `none` at every failure boundary
  (leaf continuation, out-of-range premise index, absent discharge key);
  `defeasible_rebut_typed`, `nested_undercut_typed`, and
  `mixed_path_undermine_typed` construct all three successful attack forms;
  `strict_root_rebut_rejected` pins the strict-root boundary.
* **§8 subargument closure** — a two-argument program where one attack on a
  leaf produces the direct edge onto the declared target *and* the closure
  edge onto a distinct wrapper argument containing the attacked occurrence
  (`closure_edge_direct`, `closure_edge_wrapper`), no edge onto an unrelated
  term (`closure_no_edge_unrelated`), and the expected grounded verdict under
  a concrete edge decider (`closure_grounded_verdict`): the attacker is `in`,
  the target and the wrapper are both `out`, and the wrapper's claim is
  `defeated` purely through the closure edge.

Everything here is a tiny closed fixture; proofs are `rfl`/`decide`-style
where the definitions are executable and small explicit derivations where the
judgment is relational.
-/

import Lara.Compile
import Lara.Consistency
import Lara.Check
import Lara.Check.Unit

namespace Lara.Examples

open Lara.Support Lara.Compile Lara.Check
open Lara.Check.Unit

/-! ### Fixture -/

def pA : Atom := .atom "p" .nil
def pB : Atom := .atom "q" .nil
def pC : Atom := .atom "s" .nil

def atomKeyGoldenInputs : List (Atom × String) :=
  [ (.atom "" .nil, "1:A0:1:L1:0")
  , (.atom ":" (.cons (.str "a:b") .nil), "1:A1::1:L1:18:1:S3:a:b")
  , (.atom "π" (.cons (.str "雪") .nil), "1:A2:π1:L1:18:1:S3:雪")
  , (.atom "p" (.cons (.con "z" .nil) .nil), "1:A1:p1:L1:112:1:C1:z1:L1:0")
  , (.atom "p" (.cons (.con "f" (.cons (.num "2")
      (.cons (.con "g" (.cons (.str "x") .nil)) .nil))) .nil),
      "1:A1:p1:L1:143:1:C1:f1:L1:26:1:N1:220:1:C1:g1:L1:16:1:S1:x")
  , (.atom "p" (.cons (.num "1") (.cons (.num "2") .nil)),
      "1:A1:p1:L1:26:1:N1:16:1:N1:2")
  , (.atom "p" (.cons (.num "2") (.cons (.num "1") .nil)),
      "1:A1:p1:L1:26:1:N1:26:1:N1:1") ]

def atom_key_golden_vectors : Bool :=
  atomKeyGoldenInputs.all (fun x =>
    Lara.Strict.encodeAtomKey x.1 == x.2 &&
    Lara.Strict.decodeAtomKey x.2 == some x.1)

def atom_key_malformed_rejected : Bool :=
  ["01:A0:1:L1:0", "1:A0:1:L1:0x", "1:X0:1:L1:0",
    "1:A0:1:L1:1", "1:A3:π1:L1:0"].all
      (fun s => Lara.Strict.decodeAtomKey s == none)

def ndP : Lara.ND.Formula := Lara.Strict.ndEnc id pA
def ndQ : Lara.ND.Formula := Lara.Strict.ndEnc id pB
def ndPWire : SExpr := .list [.atom "atom",
  .atom (Lara.Strict.encodeAtomKey pA)]
def ndQWire : SExpr := .list [.atom "atom",
  .atom (Lara.Strict.encodeAtomKey pB)]
def ndIdentity : CertRef := ⟨.list [.atom "lam", ndPWire,
  .list [.atom "hyp", .atom "0"]]⟩
def ndNested : CertRef := ⟨.list [.atom "lam", ndPWire,
  .list [.atom "app",
    .list [.atom "lam", ndPWire, .list [.atom "hyp", .atom "0"]],
    .list [.atom "hyp", .atom "0"]]]⟩
def ndMalformed : CertRef := ⟨.list [.atom "hyp", .atom "01"]⟩
def ndOutOfRange : CertRef := ⟨.list [.atom "hyp", .atom "2"]⟩
def ndAppFunctionFailure : CertRef := ⟨.list [.atom "app",
  .list [.atom "hyp", .atom "2"], .list [.atom "hyp", .atom "0"]]⟩
def ndAppArgumentFailure : CertRef := ⟨.list [.atom "app",
  .list [.atom "hyp", .atom "0"], .list [.atom "hyp", .atom "2"]]⟩
def ndAbortQ : CertRef := ⟨.list [.atom "abort", ndQWire,
  .list [.atom "hyp", .atom "0"]]⟩

def nd_replay_matrix : Bool :=
  Lara.Strict.ndReplay ndIdentity [] (.imp ndP ndP) &&
  Lara.Strict.ndReplay ndNested [] (.imp ndP ndP) &&
  !Lara.Strict.ndReplay ndMalformed [] ndP &&
  !Lara.Strict.ndReplay ndOutOfRange [ndP] ndP &&
  !Lara.Strict.ndReplay ⟨.list [.atom "hyp", .atom "0"]⟩ [ndP] ndQ &&
  !Lara.Strict.ndReplay ndAppFunctionFailure [.imp ndP ndQ, ndP] ndQ &&
  !Lara.Strict.ndReplay ndAppArgumentFailure [.imp ndP ndQ, ndP] ndQ &&
  Lara.Strict.ndReplay ndAbortQ [.fls] ndQ &&
  !Lara.Strict.ndReplay ndAbortQ [ndP] ndQ

def nd_decoder_matrix : Bool := decide (
    Lara.ND.decodeFormula (.atom "false") = some .fls ∧
    Lara.ND.decodeFormula ndPWire = some ndP ∧
    Lara.ND.decodeFormula (.list [.atom "imp", ndPWire, ndQWire]) =
      some (.imp ndP ndQ) ∧
    Lara.ND.decodeCert (.list [.atom "hyp", .atom "0"]) = some (.hyp 0) ∧
    Lara.ND.decodeCert ndIdentity.payload =
      some (.lam ndP (.hyp 0)) ∧
    Lara.ND.decodeCert (.list [.atom "app",
      .list [.atom "hyp", .atom "0"], .list [.atom "hyp", .atom "1"]]) =
      some (.app (.hyp 0) (.hyp 1)) ∧
    Lara.ND.decodeCert (.list [.atom "abort", ndPWire,
      .list [.atom "hyp", .atom "0"]]) =
      some (.abort ndP (.hyp 0)))

/-- Every list-form Formula constructor is rejected at one field shorter and
one field longer than its exact arity. `false` is a bare atom, so both of its
malformed list encodings are included explicitly. -/
def nd_formula_bad_arity_matrix : Bool :=
  [ .list [.atom "atom"]
  , .list [.atom "atom", .atom "P", .atom "extra"]
  , .list [.atom "false"]
  , .list [.atom "false", .atom "extra"]
  , .list [.atom "imp", ndPWire]
  , .list [.atom "imp", ndPWire, ndQWire, .atom "extra"]
  ].all (fun e => Lara.ND.decodeFormula e == none)

/-- Every certificate constructor is rejected at one field shorter and one
field longer than its exact arity. -/
def nd_cert_bad_arity_matrix : Bool :=
  [ .list [.atom "hyp"]
  , .list [.atom "hyp", .atom "0", .atom "extra"]
  , .list [.atom "lam", ndPWire]
  , .list [.atom "lam", ndPWire, .list [.atom "hyp", .atom "0"],
      .atom "extra"]
  , .list [.atom "app", .list [.atom "hyp", .atom "0"]]
  , .list [.atom "app", .list [.atom "hyp", .atom "0"],
      .list [.atom "hyp", .atom "1"], .atom "extra"]
  , .list [.atom "abort", ndPWire]
  , .list [.atom "abort", ndPWire, .list [.atom "hyp", .atom "0"],
      .atom "extra"]
  ].all (fun e => Lara.ND.decodeCert e == none)

-- These executable conformance matrices are build gates, not inert fixtures.
#guard atom_key_golden_vectors
#guard atom_key_malformed_rejected
#guard nd_replay_matrix
#guard nd_decoder_matrix
#guard nd_formula_bad_arity_matrix
#guard nd_cert_bad_arity_matrix

def numericCanon : String → String
  | "+01" => "1"
  | s => s

def numericNoisy : Atom := .atom "n" (.cons (.num "+01") .nil)
def numericCanonical : Atom := .atom "n" (.cons (.num "1") .nil)
def pArgA : Atom := .atom "p" (.cons (.con "a" .nil) .nil)
def pArgB : Atom := .atom "p" (.cons (.con "b" .nil) .nil)

/-- With predicate and arity held fixed, distinct normalized argument terms
remain distinct after ND encoding. This specifically rejects a predicate-only
encoder. -/
theorem ndEnc_distinct_atoms :
    Lara.Strict.ndEnc id pArgA ≠ Lara.Strict.ndEnc id pArgB := by
  intro h
  have he := (Lara.Strict.ndEnc_iff id pArgA pArgB).mp h
  simp [Lara.equiv, Lara.nf, Lara.nfTerms, Lara.nfTerm, pArgA, pArgB] at he

/-- Numeric spellings identified by the canonicalizer receive the same ND
encoding. -/
theorem ndEnc_numeric_canonical_equal :
    Lara.Strict.ndEnc numericCanon numericNoisy =
      Lara.Strict.ndEnc numericCanon numericCanonical := by
  apply (Lara.Strict.ndEnc_iff numericCanon numericNoisy numericCanonical).mpr
  rfl

def l1 : LeafId := ⟨"l1"⟩
def l2 : LeafId := ⟨"l2"⟩
def l3 : LeafId := ⟨"l3"⟩

def q1 : QuestionId := ⟨"q1"⟩
def q2 : QuestionId := ⟨"q2"⟩

def rMixId : RuleId := ⟨"rmix"⟩
def rWrapId : RuleId := ⟨"rwrap"⟩
def rPairId : RuleId := ⟨"rpair"⟩

def apA : APat := ⟨⟨"p"⟩, .nil⟩
def apB : APat := ⟨⟨"q"⟩, .nil⟩

def ΓEx : LeafId → Option Atom := fun l =>
  if l = l1 then some pA
  else if l = l2 then some pB
  else if l = l3 then some pC
  else none

/-- Defeasible, no premises, one mandatory (`q1`) and one optional (`q2`)
question. -/
def ruleMix : Rule :=
  { mode := .defeasible, params := [], premises := [], concl := apA
  , questions := [⟨q1, apB, true⟩, ⟨q2, apB, false⟩]
  , allowTrusted := false, certifiers := [] }

/-- Defeasible, one premise (`apA`), no questions — the wrapper rule. -/
def ruleWrap : Rule :=
  { mode := .defeasible, params := [], premises := [apA], concl := apB
  , questions := [], allowTrusted := false, certifiers := [] }

/-- Defeasible two-premise rule used to exercise set union when both children
report the same open obligation. -/
def rulePair : Rule :=
  { mode := .defeasible, params := [], premises := [apA, apA], concl := apB
  , questions := [], allowTrusted := false, certifiers := [] }

def PiEx : RuleId → Option Rule := fun r =>
  if r = rMixId then some ruleMix
  else if r = rWrapId then some ruleWrap
  else if r = rPairId then some rulePair
  else none

def certOkNone : BackendId → Digest → CertRef → List Atom → Atom → Prop :=
  fun _ _ _ _ _ => False

/-! ### Executable strict registry matrix

These fixtures use the real ND decoder and executable replay. Each resolved
backend closes over exactly one fixed theory list.
-/

/-- Exact Haskell-conformant ND identity. -/
def ndId : BackendId := ⟨"nd", 1⟩

/-- Same name, different version: a distinct (unregistered) backend identity. -/
def ndIdV2 : BackendId := ⟨"nd", 2⟩

def digestA : Digest := ⟨"sha256:theory-a"⟩
def digestB : Digest := ⟨"sha256:theory-b"⟩
def digestUnknown : Digest := ⟨"sha256:unknown"⟩

def slot0Cert : CertRef := ⟨.list [.atom "hyp", .atom "0"]⟩
def slot1Cert : CertRef := ⟨.list [.atom "hyp", .atom "1"]⟩
def rejectCert : CertRef := ⟨.list [.atom "hyp", .atom "01"]⟩

/-- The real ND backend closed over a selected fixed theory. -/
def slotBackend (canon : String → String) (theoryForms : List Atom) :
    Lara.Strict.Backend canon :=
  Lara.Strict.ndBackendWithTheory canon theoryForms

/-- `digestA` and `digestB` select distinct fixed theory lists. -/
def ndRegistered : RegisteredBackend id where
  resolve := fun h =>
    if h = digestA then some (slotBackend id [pB])
    else if h = digestB then some (slotBackend id [pC])
    else none

/-- Backend-first registry: only exact identity `nd@1` has an outer entry. -/
def registryEx : BackendRegistry id := fun β =>
  if β = ndId then some ndRegistered else none

/-- Registered backend plus exact digest accepts.  Slot 1 is the first fixed
theory entry because the source premise occupies slot 0. -/
theorem registry_exact_digest_accepts :
    certOkBOf registryEx ndId digestA slot1Cert [pA] pB = true := by
  apply (certOkBOf_iff registryEx ndId digestA slot1Cert [pA] pB).mpr
  change Lara.Strict.ndAccepts slot1Cert
    ([Lara.Strict.ndEnc id pA] ++ [Lara.Strict.ndEnc id pB])
    (Lara.Strict.ndEnc id pB)
  refine ⟨.hyp 1, ?_, .hyp rfl⟩
  have h1 : Lara.ND.decodeNat "1" = some 1 := by
    change Lara.ND.decodeNat (Nat.repr 1) = some 1
    exact Lara.ND.decodeNat_repr 1
  simp [slot1Cert, Lara.ND.decodeCert, Lara.ND.Tag.parse, h1]

/-- Registered backend plus exact digest can still reject replay. -/
theorem registry_exact_digest_rejects :
    certOkBOf registryEx ndId digestA rejectCert [pA] pB = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hacc :=
    (certOkBOf_iff registryEx ndId digestA rejectCert [pA] pB).mp h
  change Lara.Strict.ndAccepts rejectCert
    ([Lara.Strict.ndEnc id pA] ++ [Lara.Strict.ndEnc id pB])
    (Lara.Strict.ndEnc id pB) at hacc
  rcases hacc with ⟨e, hd, _⟩
  have hnone : Lara.ND.decodeCert rejectCert.payload = none := by
    simp [rejectCert, Lara.ND.decodeCert, Lara.ND.Tag.parse,
      Lara.ND.decodeNat_leading_zero_01]
  rw [hnone] at hd
  contradiction

/-- Missing outer backend entry. -/
theorem registry_backend_absent :
    certOkBOf registryEx ⟨"other", 1⟩ digestA slot1Cert [pA] pB = false := by
  decide

/-- Backend name alone is not identity: `nd@2` cannot use `nd@1`. -/
theorem registry_version_mismatch :
    certOkBOf registryEx ndIdV2 digestA slot1Cert [pA] pB = false := by
  decide

/-- Present backend, unknown inner digest. -/
theorem registry_digest_unknown :
    certOkBOf registryEx ndId digestUnknown slot1Cert [pA] pB = false := by
  decide

/-- The successful Boolean result produces mathematical acceptance. -/
theorem registry_success_bridge :
    certOkOf registryEx ndId digestA slot1Cert [pA] pB :=
  (certOkBOf_iff registryEx ndId digestA slot1Cert [pA] pB).mp
    registry_exact_digest_accepts

/-- Adequacy also rules out proposition-level acceptance on a missing outer
lookup. -/
theorem registry_missing_bridge :
    ¬ certOkOf registryEx ndIdV2 digestA slot1Cert [pA] pB := by
  intro hacc
  have hb :=
    (certOkBOf_iff registryEx ndIdV2 digestA slot1Cert [pA] pB).mpr hacc
  rw [registry_version_mismatch] at hb
  exact Bool.noConfusion hb

/-- Replay sees source premises before fixed theory entries. -/
theorem registry_premises_before_theory :
    certOkBOf registryEx ndId digestA slot0Cert [pA] pA = true := by
  apply (certOkBOf_iff registryEx ndId digestA slot0Cert [pA] pA).mpr
  change Lara.Strict.ndAccepts slot0Cert
    ([Lara.Strict.ndEnc id pA] ++ [Lara.Strict.ndEnc id pB])
    (Lara.Strict.ndEnc id pA)
  refine ⟨.hyp 0, ?_, .hyp rfl⟩
  have h0 : Lara.ND.decodeNat "0" = some 0 := by
    change Lara.ND.decodeNat (Nat.repr 0) = some 0
    exact Lara.ND.decodeNat_repr 0
  simp [slot0Cert, Lara.ND.decodeCert, Lara.ND.Tag.parse, h0]

/-- Distinct digest fixtures really close over distinct fixed theories, and the
same slot-1 certificate observes that selection after the premise prefix. -/
theorem registry_fixed_theory_order :
    certOkBOf registryEx ndId digestA slot1Cert [pA] pB = true ∧
    certOkBOf registryEx ndId digestB slot1Cert [pA] pB = false := by
  refine ⟨registry_exact_digest_accepts, ?_⟩
  apply Bool.eq_false_iff.mpr
  intro h
  have hacc :=
    (certOkBOf_iff registryEx ndId digestB slot1Cert [pA] pB).mp h
  change Lara.Strict.ndAccepts slot1Cert
    ([Lara.Strict.ndEnc id pA] ++ [Lara.Strict.ndEnc id pC])
    (Lara.Strict.ndEnc id pB) at hacc
  rcases hacc with ⟨e, hd, ht⟩
  have h1 : Lara.ND.decodeNat "1" = some 1 := by
    change Lara.ND.decodeNat (Nat.repr 1) = some 1
    exact Lara.ND.decodeNat_repr 1
  have hd1 : Lara.ND.decodeCert slot1Cert.payload = some (.hyp 1) := by
    simp [slot1Cert, Lara.ND.decodeCert, Lara.ND.Tag.parse, h1]
  rw [hd1] at hd
  injection hd with he
  subst e
  cases ht with
  | hyp hlookup =>
    have heq : Lara.Strict.ndEnc id pC = Lara.Strict.ndEnc id pB := by
      simpa [Lara.ND.lookup] using Option.some.inj hlookup
    have hequiv := (Lara.Strict.ndEnc_iff id pC pB).mp heq
    simp [pC, pB, Lara.equiv, Lara.nf] at hequiv

/-! ### §7.1 position-lookup boundaries -/

def tDis : SupportTerm := .leaf l2
def tI : SupportTerm := .inst rWrapId [] [.leaf l1] [(q1, tDis)] [] .none
def tNest : SupportTerm := .inst rWrapId [] [tI] [] [] .none

/-- Traversal order and every failure boundary of `u@π`, concretely. -/
theorem subterm_boundaries :
    Attack.subterm tI [] = some tI ∧
    Attack.subterm tI [.prem 0] = some (.leaf l1) ∧
    Attack.subterm tI [.ques q1] = some tDis ∧
    Attack.subterm tI [.prem 1] = none ∧
    Attack.subterm tI [.ques q2] = none ∧
    Attack.subterm (.leaf l1) [.prem 0] = none ∧
    Attack.subterm tI [.prem 0, .prem 0] = none ∧
    Attack.subterm tNest [.prem 0, .ques q1] = some tDis := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩ <;>
    simp [tI, tNest, tDis, Attack.subterm, Attack.lookupDis, q1, q2]

/-! ### §6.1 obligation accounting, concretely -/

/-- Instance of `ruleMix` with both questions open as explicit holes. -/
def tMix : SupportTerm := .inst rMixId [] [] [] [q1, q2] .none

/-- The shared vacuous premise/discharge typing hypotheses for childless
instances. -/
theorem no_prems {canon Pi Gamma CertOk} :
    ∀ (i : Nat) (w : SupportTerm) (A : Atom) (O : List QuestionId),
      ([] : List SupportTerm)[i]? = some w → ([] : List Atom)[i]? = some A →
      ([] : List (List QuestionId))[i]? = some O →
      HasSupport canon Pi Gamma CertOk w A O := by
  intro i w A O hw _ _
  simp at hw

theorem no_dis {canon Pi Gamma CertOk} :
    ∀ (j : Nat) (q : QuestionId) (w : SupportTerm) (A : Atom)
      (O : List QuestionId),
      ([] : List (QuestionId × SupportTerm))[j]? = some (q, w) →
      ([] : List Atom)[j]? = some A →
      ([] : List (List QuestionId))[j]? = some O →
      HasSupport canon Pi Gamma CertOk w A O := by
  intro j q w A O hD _ _
  simp at hD

theorem sideMix : InstSide id PiEx certOkNone rMixId [] ruleMix [] [] [q1, q2]
    .none [] [] [] [] [] pA where
  rule := by simp [PiEx]
  θNodup := by simp
  θDom := by simp [ruleMix]
  prems := rfl
  concl := by decide
  lenAs := rfl
  lenCs := rfl
  lenOs := rfl
  premEq := by intro i A B hA _; simp at hA
  lenDCs := rfl
  lenDOs := rfl
  ans := by intro j q w A hD _; simp at hD
  qNodup := by simp [questionNames, ruleMix, q1, q2]
  dNodup := by simp
  hNodup := by simp [q1, q2]
  cover := by
    intro qd hqd
    simp only [ruleMix, List.mem_cons, List.not_mem_nil, or_false] at hqd
    rcases hqd with rfl | rfl
    · exact Or.inr (by simp)
    · exact Or.inr (by simp)
  disj := by intro n hn; simp at hn
  keysD := by intro n hn; simp at hn
  keysH := by
    intro n hn
    simpa [questionNames, ruleMix] using hn
  strictNoQ := by intro h; simp [ruleMix] at h
  assur := .defeasible rfl

/-- **Mixed holes:** open mandatory `q1` + open optional `q2` contribute
exactly `[q1]` — the optional hole is accounted for (it is in `H`) but adds
no obligation. -/
theorem mixed_holes_obligations :
    HasSupport id PiEx ΓEx certOkNone tMix pA [q1] :=
  (by decide :
      collectObligations [] [] ruleMix [q1, q2] = [q1]) ▸
    HasSupport.inst sideMix no_prems no_dis

/-- Wrapper instance whose single premise is the hole-carrying `tMix`. -/
def tUse : SupportTerm := .inst rWrapId [] [tMix] [] [] .none

theorem sideUse : InstSide id PiEx certOkNone rWrapId [] ruleWrap [tMix] [] []
    .none [pA] [pA] [[q1]] [] [] pB where
  rule := by simp [PiEx, rMixId, rWrapId]
  θNodup := by simp
  θDom := by simp [ruleWrap]
  prems := by decide
  concl := by decide
  lenAs := rfl
  lenCs := rfl
  lenOs := rfl
  premEq := by
    intro i A B hA hB
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hA hB
      subst hA; subst hB
      exact equiv_refl id pA
    | succ j => simp at hA
  lenDCs := rfl
  lenDOs := rfl
  ans := by intro j q w A hD _; simp at hD
  qNodup := by simp [questionNames, ruleWrap]
  dNodup := by simp
  hNodup := by simp
  cover := by intro qd hqd; simp [ruleWrap] at hqd
  disj := by intro n hn; simp at hn
  keysD := by intro n hn; simp at hn
  keysH := by intro n hn; simp at hn
  strictNoQ := by intro h; simp [ruleWrap] at h
  assur := .defeasible rfl

/-- **Nested obligations propagate:** the premise subterm's open mandatory
obligation surfaces in the parent's `O`. -/
theorem nested_obligation_propagates :
    HasSupport id PiEx ΓEx certOkNone tUse pB [q1] :=
  (by decide :
      collectObligations [[q1]] [] ruleWrap [] = [q1]) ▸
    HasSupport.inst sideUse
      (by
        intro i w A O hw hA hO
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hw hA hO
          subst hw; subst hA; subst hO
          exact mixed_holes_obligations
        | succ j => simp at hw)
      no_dis

/-- A `ruleMix` instance that discharges mandatory `q1` with `tUse`, whose own
premise carries the open obligation `q1`; optional `q2` remains an open hole. -/
def tDisUse : SupportTerm :=
  .inst rMixId [] [] [(q1, tUse)] [q2] .none

theorem sideDisUse :
    InstSide id PiEx certOkNone rMixId [] ruleMix [] [(q1, tUse)] [q2]
      .none [] [] [] [pB] [[q1]] pA where
  rule := by simp [PiEx]
  θNodup := by simp
  θDom := by simp [ruleMix]
  prems := rfl
  concl := by decide
  lenAs := rfl
  lenCs := rfl
  lenOs := rfl
  premEq := by intro i A B hA _; simp at hA
  lenDCs := rfl
  lenDOs := rfl
  ans := by
    intro j q w A hD hA
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hD hA
      injection hD with hq hw
      subst q; subst w; subst A
      exact ⟨⟨q1, apB, true⟩, by simp [ruleMix], rfl,
        pB, by decide, equiv_refl id pB⟩
    | succ j => simp at hD
  qNodup := by simp [questionNames, ruleMix, q1, q2]
  dNodup := by simp
  hNodup := by simp
  cover := by
    intro qd hqd
    simp only [ruleMix, List.mem_cons, List.not_mem_nil, or_false] at hqd
    rcases hqd with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  disj := by
    intro n hn hH
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hn hH
    rw [hn] at hH
    simp [q1, q2] at hH
  keysD := by
    intro n hn
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hn
    subst n
    simp [questionNames, ruleMix]
  keysH := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    subst n
    simp [questionNames, ruleMix]
  strictNoQ := by intro h; simp [ruleMix] at h
  assur := .defeasible rfl

/-- **Discharge obligations propagate:** obligations generated inside a
discharging support term are included in the parent instance's exact `O`. -/
theorem discharge_obligation_propagates :
    HasSupport id PiEx ΓEx certOkNone tDisUse pA [q1] :=
  (by decide :
      collectObligations [] [[q1]] ruleMix [q2] = [q1]) ▸
    HasSupport.inst sideDisUse no_prems
      (by
        intro j q w A O hD hA hO
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hD hA hO
          injection hD with hq hw
          subst q; subst w; subst A; subst O
          exact nested_obligation_propagates
        | succ j => simp at hD)

/-- Two child terms both report `q1`; §6.1's set union reports it once. -/
def tPair : SupportTerm := .inst rPairId [] [tMix, tMix] [] [] .none

theorem sidePair :
    InstSide id PiEx certOkNone rPairId [] rulePair [tMix, tMix] [] []
      .none [pA, pA] [pA, pA] [[q1], [q1]] [] [] pB where
  rule := by simp [PiEx, rMixId, rWrapId, rPairId]
  θNodup := by simp
  θDom := by simp [rulePair]
  prems := by decide
  concl := by decide
  lenAs := rfl
  lenCs := rfl
  lenOs := rfl
  premEq := by
    intro i A B hA hB
    cases i with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hA hB
        subst A; subst B
        exact equiv_refl id pA
    | succ i =>
        cases i with
        | zero =>
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
              Option.some.injEq] at hA hB
            subst A; subst B
            exact equiv_refl id pA
        | succ j => simp at hA
  lenDCs := rfl
  lenDOs := rfl
  ans := by intro j q w A hD _; simp at hD
  qNodup := by simp [questionNames, rulePair]
  dNodup := by simp
  hNodup := by simp
  cover := by intro qd hqd; simp [rulePair] at hqd
  disj := by intro n hn; simp at hn
  keysD := by intro n hn; simp at hn
  keysH := by intro n hn; simp at hn
  strictNoQ := by intro h; simp [rulePair] at h
  assur := .defeasible rfl

theorem repeated_obligation_deduplicated :
    HasSupport id PiEx ΓEx certOkNone tPair pB [q1] :=
  (by decide :
      collectObligations [[q1], [q1]] [] rulePair [] = [q1]) ▸
    HasSupport.inst sidePair
      (by
        intro i w A O hw hA hO
        cases i with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hw hA hO
            subst w; subst A; subst O
            exact mixed_holes_obligations
        | succ i =>
            cases i with
            | zero =>
                simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
                  Option.some.injEq] at hw hA hO
                subst w; subst A; subst O
                exact mixed_holes_obligations
            | succ j => simp at hw)
      no_dis

/-- **Missing accounting rejects:** dropping the optional question from the
hole set (only `[q1]` declared open) makes the `ruleMix` instance untypable —
every declared question must be in `D ⊎ H` (§4.2/§6.1). -/
theorem missing_question_rejected :
    ¬ ∃ C O, HasSupport id PiEx ΓEx certOkNone
        (.inst rMixId [] [] [] [q1] .none) C O := by
  rintro ⟨C, O, h⟩
  cases h with
  | @inst _ _ _ _ _ _ r' _ _ _ _ _ _ hside _ _ =>
    have hr : r' = ruleMix := by
      have := hside.rule
      simp only [PiEx] at this
      exact Option.some.inj this.symm
    subst hr
    have hcov := hside.cover ⟨q2, apB, false⟩ (by simp [ruleMix])
    rcases hcov with h | h
    · simp at h
    · simp [q1, q2] at h

/-- **Overlapping accounting rejects:** a question cannot occur in both the
discharge map and the hole set. This pins the disjoint half of `D ⊎ H`. -/
theorem overlapping_question_rejected :
    ¬ ∃ C O, HasSupport id PiEx ΓEx certOkNone
        (.inst rMixId [] [] [(q1, .leaf l2)] [q1, q2] .none) C O := by
  rintro ⟨C, O, h⟩
  cases h with
  | @inst _ _ _ _ _ _ _ _ _ _ _ _ _ hside _ _ =>
    exact hside.disj q1 (by simp) (by simp)

/-! ### Executable support-checker conformance -/

def xCheck : VarId := ⟨"x-check"⟩
def yCheck : VarId := ⟨"y-check"⟩
def tZero : Term := .num "0"
def apX : APat := ⟨⟨"p"⟩, .cons (.var xCheck) .nil⟩
def apY : APat := ⟨⟨"p"⟩, .cons (.var yCheck) .nil⟩

def rParamPremId : RuleId := ⟨"r-param-prem"⟩
def rParamConclId : RuleId := ⟨"r-param-concl"⟩
def rStrictTrustedId : RuleId := ⟨"r-strict-trusted"⟩
def rStrictNoTrustId : RuleId := ⟨"r-strict-no-trust"⟩
def rStrictQuestionId : RuleId := ⟨"r-strict-question"⟩
def rCertId : RuleId := ⟨"r-cert"⟩
def rCertNoneId : RuleId := ⟨"r-cert-none"⟩
def rCertOtherId : RuleId := ⟨"r-cert-other"⟩
def rCertDigestId : RuleId := ⟨"r-cert-digest"⟩
def rBadAnswerId : RuleId := ⟨"r-bad-answer"⟩
def rDupQuestionId : RuleId := ⟨"r-dup-question"⟩
def otherBackend : BackendId := ⟨"other", 1⟩

def ruleParamPrem : Rule :=
  { mode := .defeasible, params := [xCheck], premises := [apY], concl := apA
  , questions := [], allowTrusted := false, certifiers := [] }

def ruleParamConcl : Rule :=
  { mode := .defeasible, params := [xCheck], premises := [], concl := apY
  , questions := [], allowTrusted := false, certifiers := [] }

def ruleStrictTrusted : Rule :=
  { mode := .strict, params := [], premises := [], concl := apA
  , questions := [], allowTrusted := true, certifiers := [] }

def ruleStrictNoTrust : Rule :=
  { ruleStrictTrusted with allowTrusted := false }

def ruleStrictQuestion : Rule :=
  { ruleStrictTrusted with questions := [⟨q1, apB, true⟩] }

def ruleCert : Rule :=
  { mode := .strict, params := [], premises := [apA], concl := apB
  , questions := [], allowTrusted := false
  , certifiers := [(ndId, digestA)] }

def ruleCertNone : Rule := { ruleCert with certifiers := [] }
def ruleCertOther : Rule :=
  { ruleCert with certifiers := [(otherBackend, digestA)] }
def ruleCertDigest : Rule :=
  { ruleCert with certifiers := [(ndId, digestUnknown)] }

def ruleBadAnswer : Rule :=
  { mode := .defeasible, params := [xCheck], premises := [], concl := apA
  , questions := [⟨q1, apY, true⟩], allowTrusted := false, certifiers := [] }

def ruleDupQuestion : Rule :=
  { ruleMix with questions := [⟨q1, apB, true⟩, ⟨q1, apB, false⟩] }

def PiCheck : RuleId → Option Rule := fun rn =>
  if rn = rParamPremId then some ruleParamPrem
  else if rn = rParamConclId then some ruleParamConcl
  else if rn = rStrictTrustedId then some ruleStrictTrusted
  else if rn = rStrictNoTrustId then some ruleStrictNoTrust
  else if rn = rStrictQuestionId then some ruleStrictQuestion
  else if rn = rCertId then some ruleCert
  else if rn = rCertNoneId then some ruleCertNone
  else if rn = rCertOtherId then some ruleCertOther
  else if rn = rCertDigestId then some ruleCertDigest
  else if rn = rBadAnswerId then some ruleBadAnswer
  else if rn = rDupQuestionId then some ruleDupQuestion
  else PiEx rn

def PiCert : RuleId → Option Rule := fun rn =>
  if rn = rCertId then some ruleCert else none

theorem check_declared_leaf :
    inferSupport PiCheck ΓEx registryEx .root (.leaf l1) =
      .ok ⟨pA, []⟩ := by rfl

theorem check_mixed_holes :
    inferSupport PiCheck ΓEx registryEx .root tMix =
      .ok ⟨pA, [q1]⟩ := by rfl

theorem check_nested_obligations :
    inferSupport PiCheck ΓEx registryEx .root tUse =
      .ok ⟨pB, [q1]⟩ := by rfl

theorem check_discharge_propagation :
    inferSupport PiCheck ΓEx registryEx .root tDisUse =
      .ok ⟨pA, [q1]⟩ := by rfl

theorem check_obligation_deduplication :
    inferSupport PiCheck ΓEx registryEx .root tPair =
      .ok ⟨pB, [q1]⟩ := by rfl

theorem check_missing_question :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rMixId [] [] [] [q1] .none) =
      .error (.R5 .root
        (.uncovered [q1, q2] [] [q1])) := by rfl

theorem check_question_overlap :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rMixId [] [] [(q1, .leaf l2)] [q1, q2] .none) =
      .error (.R5 .root
        (.overlap [q1] [q1, q2])) := by rfl

theorem check_premise_mismatch :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rWrapId [] [.leaf l2] [] [] .none) =
      .error (.R4 (.premise .root 0) (.mismatch pA pB)) := by rfl

theorem check_discharge_mismatch :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rMixId [] [] [(q1, .leaf l1)] [q2] .none) =
      .error (.R6 (.question .root q1)
        (.conclusionMismatch q1 pB pA)) := by rfl

theorem check_discharge_precedes_question_accounting :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rMixId [] [] [(q1, .leaf l1)] [] .none) =
      .error (.R6 (.question .root q1)
        (.conclusionMismatch q1 pB pA)) := by rfl

theorem check_missing_leaf :
    inferSupport PiCheck ΓEx registryEx .root (.leaf ⟨"missing"⟩) =
      .error (.R1 .root (.missingLeaf ⟨"missing"⟩)) := by rfl

theorem check_missing_rule_precedence :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst ⟨"missing"⟩ [(xCheck, tZero), (xCheck, tZero)]
        [.leaf ⟨"missing"⟩] [] [] .none) =
      .error (.R1 .root (.missingRule ⟨"missing"⟩)) := by rfl

theorem check_duplicate_substitution_precedence :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rParamPremId [(xCheck, tZero), (xCheck, tZero)]
        [.leaf ⟨"missing"⟩] [] [] .none) =
      .error (.R3 .root
        (.duplicateKeys [xCheck, xCheck])) := by rfl

theorem check_substitution_domain :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rParamPremId [] [] [] [] .none) =
      .error (.R3 .root (.domainMismatch [] [xCheck])) := by rfl

theorem check_substitution_extra_binding :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rWrapId [(xCheck, tZero)] [] [] [] .none) =
      .error (.R3 .root (.domainMismatch [xCheck] [])) := by rfl

theorem check_premise_instantiation :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rParamPremId [(xCheck, tZero)] [] [] [] .none) =
      .error (.R3 .root
        (.premiseInstantiation [apY])) := by rfl

theorem check_conclusion_instantiation :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rParamConclId [(xCheck, tZero)] [] [] [] .none) =
      .error (.R3 .root
        (.conclusionInstantiation apY)) := by rfl

theorem check_too_few_premises :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rWrapId [] [] [] [] .none) =
      .error (.R4 .root (.count 1 0)) := by rfl

theorem check_too_many_premises :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rWrapId [] [.leaf l1, .leaf l1] [] [] .none) =
      .error (.R4 .root (.count 1 2)) := by rfl

theorem check_child_error_precedes_parent_shape :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rWrapId [] [.leaf ⟨"missing"⟩, .leaf l1] [] [] .none) =
      .error (.R1 (.premise .root 0)
        (.missingLeaf ⟨"missing"⟩)) := by rfl

theorem check_duplicate_declarations :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rDupQuestionId [] [] [] [q1] .none) =
      .error (.R5 .root
        (.duplicateDeclarations [q1, q1])) := by rfl

theorem check_duplicate_discharges :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rMixId [] [] [(q1, .leaf l2), (q1, .leaf l2)] [q2] .none) =
      .error (.R5 .root
        (.duplicateDischarges [q1, q1])) := by rfl

theorem check_duplicate_holes :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rMixId [] [] [] [q1, q1, q2] .none) =
      .error (.R5 .root
        (.duplicateHoles [q1, q1, q2])) := by rfl

theorem check_undeclared_discharge :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rMixId [] [] [(q1, .leaf l2), (⟨"junk"⟩, .leaf l2)]
        [q2] .none) =
      .error (.R5 .root
        (.undeclaredDischarge [q1, ⟨"junk"⟩] [q1, q2])) := by rfl

theorem check_undeclared_hole :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rMixId [] [] [] [q1, q2, ⟨"junk"⟩] .none) =
      .error (.R5 .root
        (.undeclaredHole [q1, q2, ⟨"junk"⟩] [q1, q2])) := by rfl

theorem check_answer_instantiation :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rBadAnswerId [(xCheck, tZero)] []
        [(q1, .leaf l2)] [] .none) =
      .error (.R6 (.question .root q1)
        (.answerInstantiation q1 apY)) := by rfl

theorem check_strict_questions :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rStrictQuestionId [] [] [] [q1] .trusted) =
      .error (.R7 .root (.questionsPresent [] [q1])) := by rfl

theorem check_strict_trusted_success :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rStrictTrustedId [] [] [] [] .trusted) =
      .ok ⟨pA, []⟩ := by rfl

theorem check_strict_cert_success :
    inferSupport PiCert ΓEx registryEx .root
      (.inst rCertId [] [.leaf l1] [] [] (.cert ndId digestA slot1Cert)) =
      .ok ⟨pB, []⟩ := by
  have hcert : certOkBOf registryEx ndId digestA slot1Cert
      [Atom.atom "p" .nil] (Atom.atom "q" .nil) = true := by
    simpa [pA, pB] using registry_exact_digest_accepts
  have hequiv : equiv id pA (Atom.atom "p" .nil) := by
    rfl
  simp [inferSupport, inferSupportRaw, inferPremisesRaw, inferDischargesRaw,
    PiCert, ruleCert, ΓEx, requireB, instAPats, instAPat, instPats,
    Bind.bind, Except.bind, Pure.pure, Except.pure,
    apA, apB, pB, l1, substDomainB, atomsEquivB, questionNames, hequiv,
    collectObligations, unionAll, dedupQuestions, openMandatory,
    mandatoryNames, memB,
    knownAnswersOkB, strictNoQuestionB, assuranceOkB,
    hcert]

theorem check_assurance_wrong_mode :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rStrictTrustedId [] [] [] [] .none) =
      .error (.R7 .root
        (.wrongMode .strict .none)) := by rfl

theorem check_assurance_trusted_disallowed :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rStrictNoTrustId [] [] [] [] .trusted) =
      .error (.R7 .root .trustedDisallowed) := by rfl

theorem check_assurance_unallowlisted :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rCertNoneId [] [.leaf l1] [] []
        (.cert ndId digestA slot1Cert)) =
      .error (.R7 .root
        (.certifierUnallowlisted ndId digestA)) := by rfl

theorem check_assurance_backend_missing :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rCertOtherId [] [.leaf l1] [] []
        (.cert otherBackend digestA slot1Cert)) =
      .error (.R13 .root
        (.backendMissing otherBackend)) := by rfl

theorem check_assurance_digest_missing :
    inferSupport PiCheck ΓEx registryEx .root
      (.inst rCertDigestId [] [.leaf l1] [] []
        (.cert ndId digestUnknown slot1Cert)) =
      .error (.R13 .root
        (.digestMissing ndId digestUnknown)) := by rfl

theorem check_assurance_replay_rejected :
    inferSupport PiCert ΓEx registryEx .root
      (.inst rCertId [] [.leaf l1] [] [] (.cert ndId digestA rejectCert)) =
      .error (.R13 .root
        (.replayRejected ndId digestA rejectCert)) := by
  have hcert : certOkBOf registryEx ndId digestA rejectCert
      [Atom.atom "p" .nil] (Atom.atom "q" .nil) = false := by
    simpa [pA, pB] using registry_exact_digest_rejects
  have hequiv : equiv id pA (Atom.atom "p" .nil) := by
    rfl
  simp [inferSupport, inferSupportRaw, inferPremisesRaw, inferDischargesRaw,
    PiCert, ruleCert, ΓEx, requireB, instAPats, instAPat, instPats,
    Bind.bind, Except.bind, Pure.pure, Except.pure,
    apA, apB, l1, substDomainB, atomsEquivB, questionNames, hequiv,
    memB, knownAnswersOkB, strictNoQuestionB, assuranceOkB,
    hcert, assuranceError, registryEx, ndRegistered]

/-! ### §7.1 successful attacks at nested positions -/

/-- Policy fixture with an undercut exception for `rWrap` and a contrary from
`pA` to `pB`, used to exercise successful nested attacks. -/
def dpPos : Attack.DefeatPolicy :=
  ⟨[(apA, apB)], [(rWrapId, apB)]⟩

def dpRebut : Attack.DefeatPolicy :=
  ⟨[(apB, apA)], []⟩

def kRebut : Attack.Attack := .rebut (.leaf l2) tMix

/-- Successful rebut construction against a defeasible-root instance. -/
theorem defeasible_rebut_typed :
    Attack.HasAttack id PiEx ΓEx certOkNone dpRebut kRebut := by
  refine Attack.HasAttack.rebut
    (w := .leaf l2) (rn := rMixId) (θ := []) (ws := [])
    (D := []) (H := [q1, q2]) (a := .none)
    (r := ruleMix) (Cw := pB) (Cu := pA) (Ow := [])
    (.leaf (by decide))
    (by simp [PiEx])
    rfl
    (by decide)
    ⟨(apB, apA), by simp [dpRebut], [], pB, pA, by decide, by decide,
      equiv_refl id pB, equiv_refl id pA⟩

def rStrictId : RuleId := ⟨"rstrict"⟩

def ruleStrict : Rule :=
  { mode := .strict, params := [], premises := [], concl := apA
  , questions := [], allowTrusted := true, certifiers := [] }

def PiStrict : RuleId → Option Rule := fun r =>
  if r = rStrictId then some ruleStrict else PiEx r

def strictTarget : SupportTerm :=
  .inst rStrictId [] [] [] [] .trusted

/-- The same contrary source cannot rebut a strict-root target. -/
theorem strict_root_rebut_rejected :
    ¬ Attack.HasAttack id PiStrict ΓEx certOkNone dpRebut
      (.rebut (.leaf l2) strictTarget) := by
  intro h
  have hmode := Attack.rebut_top_defeasible
    (r := ruleStrict) h (by simp [PiStrict])
  simp [ruleStrict] at hmode

def kNestedUndercut : Attack.Attack :=
  .undercut (.leaf l2) tNest [.prem 0]

/-- A successful undercut at nested premise position `[prem 0]`. -/
theorem nested_undercut_typed :
    Attack.HasAttack id PiEx ΓEx certOkNone dpPos kNestedUndercut :=
  by
    refine Attack.HasAttack.undercut
      (w := .leaf l2) (u := tNest) (π := [.prem 0])
      (rn := rWrapId) (θ := []) (ws := [.leaf l1])
      (D := [(q1, tDis)]) (H := []) (a := .none)
      (r := ruleWrap) (E := apB) (e := pB) (Cw := pB) (Ow := [])
      (.leaf (by decide))
      (by simp [tNest, tI, Attack.subterm])
      (by simp [PiEx, rMixId, rWrapId])
      rfl
      (by simp [dpPos])
      (by decide)
      (equiv_refl id pB)

def kMixedUndermine : Attack.Attack :=
  .undermine (.leaf l1) tNest [.prem 0, .ques q1]

/-- A successful undermine after mixed premise/question traversal. -/
theorem mixed_path_undermine_typed :
    Attack.HasAttack id PiEx ΓEx certOkNone dpPos kMixedUndermine :=
  by
    refine Attack.HasAttack.undermine
      (w := .leaf l1) (u := tNest) (π := [.prem 0, .ques q1])
      (l := l2) (pl := pB) (Cw := pA) (Ow := [])
      (.leaf (by decide))
      (by simp [tNest, tI, tDis, Attack.subterm, Attack.lookupDis, q1])
      (by decide)
      ⟨(apA, apB), by simp [dpPos], [], pA, pB, by decide, by decide,
        equiv_refl id pA, equiv_refl id pB⟩

/-! ### Executable contrary and positional-attack matrix -/

def vx : VarId := ⟨"X"⟩
def apPX : APat := ⟨⟨"p"⟩, .cons (.var vx) .nil⟩
def apQX : APat := ⟨⟨"q"⟩, .cons (.var vx) .nil⟩
def apPXX : APat :=
  ⟨⟨"p"⟩, .cons (.var vx) (.cons (.var vx) .nil)⟩
def ta : Term := .con "a" .nil
def tb : Term := .con "b" .nil
def pTa : Atom := .atom "p" (.cons ta .nil)
def qTa : Atom := .atom "q" (.cons ta .nil)
def qTb : Atom := .atom "q" (.cons tb .nil)
def pTaTa : Atom := .atom "p" (.cons ta (.cons ta .nil))
def pTaTb : Atom := .atom "p" (.cons ta (.cons tb .nil))

def dpShared : Attack.DefeatPolicy := ⟨[(apPX, apQX)], []⟩
def dpRepeated : Attack.DefeatPolicy := ⟨[(apPXX, apB)], []⟩

theorem contrary_shared_substitution :
    Attack.contraryMatchB id dpShared pTa qTa = true := by decide

theorem contrary_shared_substitution_rejects :
    Attack.contraryMatchB id dpShared pTa qTb = false := by decide

theorem contrary_repeated_variable :
    Attack.contraryMatchB id dpRepeated pTaTa pB = true := by decide

theorem contrary_repeated_variable_rejects :
    Attack.contraryMatchB id dpRepeated pTaTb pB = false := by decide

def apNumX : APat :=
  ⟨⟨"n"⟩, .cons (.num "+01") .nil⟩
def dpNumeric : Attack.DefeatPolicy := ⟨[(apNumX, apB)], []⟩

theorem contrary_canonical_numeric :
    Attack.contraryMatchB numericCanon dpNumeric numericCanonical pB = true :=
  by decide

def stepCanon : String → String
  | "a" => "b"
  | "b" => "c"
  | s => s

def pNumAB : Atom :=
  .atom "p" (.cons (.num "a") (.cons (.num "b") .nil))

/-- A matcher that normalized its stored binding again would incorrectly
accept this pair (`canon (canon "a") = "c"`). -/
theorem contrary_nonidempotent_repeated_rejects :
    Attack.contraryMatchB stepCanon dpRepeated pNumAB pB = false := by decide

theorem contrary_constructor_arity_rejects :
    Attack.contraryMatchB id dpShared
      (.atom "p" (.cons (.con "a" (.cons ta .nil)) .nil)) qTa = false := by
  decide

theorem check_rebut_success :
    checkAttack PiEx ΓEx registryEx dpRebut kRebut = .ok () := by rfl

theorem check_nested_undercut_success :
    checkAttack PiEx ΓEx registryEx dpPos kNestedUndercut = .ok () := by rfl

theorem check_mixed_undermine_success :
    checkAttack PiEx ΓEx registryEx dpPos kMixedUndermine = .ok () := by rfl

theorem check_rebut_strict_root :
    checkAttack PiStrict ΓEx registryEx dpRebut
      (.rebut (.leaf l2) strictTarget) =
      .error (.R11 .root [] .rebut (.strictTarget rStrictId)) := by rfl

theorem check_undercut_strict_occurrence :
    checkAttack PiStrict ΓEx registryEx dpPos
      (.undercut (.leaf l2) strictTarget []) =
      .error (.R11 .root [] .undercut (.strictTarget rStrictId)) := by rfl

theorem check_undercut_undefined_position :
    checkAttack PiEx ΓEx registryEx dpPos
      (.undercut (.leaf l2) tNest [.prem 9]) =
      .error (.R10 .root [.prem 9] .undercut .undefinedPosition) := by rfl

theorem check_undermine_undefined_position :
    checkAttack PiEx ΓEx registryEx dpPos
      (.undermine (.leaf l1) tNest [.ques q2]) =
      .error (.R10 .root [.ques q2] .undermine .undefinedPosition) := by rfl

theorem check_undercut_wrong_occurrence :
    checkAttack PiEx ΓEx registryEx dpPos
      (.undercut (.leaf l2) tNest [.prem 0, .ques q1]) =
      .error (.R10 .root [.prem 0, .ques q1] .undercut
        (.wrongOccurrenceKind .rule .leaf)) := by rfl

theorem check_undermine_wrong_occurrence :
    checkAttack PiEx ΓEx registryEx dpPos
      (.undermine (.leaf l1) tNest [.prem 0]) =
      .error (.R10 .root [.prem 0] .undermine
        (.wrongOccurrenceKind .leaf .rule)) := by rfl

theorem check_rebut_wrong_occurrence :
    checkAttack PiEx ΓEx registryEx dpRebut
      (.rebut (.leaf l2) (.leaf l1)) =
      .error (.R10 .root [] .rebut
        (.wrongOccurrenceKind .rule .leaf)) := by rfl

theorem check_rebut_missing_contrary :
    checkAttack PiEx ΓEx registryEx dpPos kRebut =
      .error (.R11 .root [] .rebut (.missingContrary pB pA)) := by rfl

theorem check_undermine_missing_contrary :
    checkAttack PiEx ΓEx registryEx dpRebut
      (.undermine (.leaf l1) (.leaf l2) []) =
      .error (.R11 .root [] .undermine
        (.missingContrary pA pB)) := by rfl

def rAbsent : RuleId := ⟨"absent-target"⟩
def absentTarget : SupportTerm := .inst rAbsent [] [] [] [] .none

theorem check_rebut_missing_target_rule :
    checkAttack PiEx ΓEx registryEx dpRebut
      (.rebut (.leaf l2) absentTarget) =
      .error (.R11 .root [] .rebut (.missingTargetRule rAbsent)) := by rfl

theorem check_undercut_missing_target_rule :
    checkAttack PiEx ΓEx registryEx dpPos
      (.undercut (.leaf l2) absentTarget []) =
      .error (.R11 .root [] .undercut (.missingTargetRule rAbsent)) := by rfl

def rBadConclId : RuleId := ⟨"bad-concl-target"⟩
def ruleBadConcl : Rule :=
  { ruleWrap with params := [vx], concl := apPX }
def PiAttackBad : RuleId → Option Rule := fun rn =>
  if rn = rBadConclId then some ruleBadConcl else PiEx rn
def badConclTarget : SupportTerm :=
  .inst rBadConclId [] [] [] [] .none

theorem check_rebut_target_conclusion_instantiation :
    checkAttack PiAttackBad ΓEx registryEx dpRebut
      (.rebut (.leaf l2) badConclTarget) =
      .error (.R11 .root [] .rebut
        (.targetConclusionInstantiation rBadConclId apPX)) := by rfl

def apQVar : APat := ⟨⟨"q"⟩, .cons (.var vx) .nil⟩
def dpBadException : Attack.DefeatPolicy :=
  ⟨[], [(rWrapId, apQVar)]⟩

theorem check_undercut_exception_instantiation :
    checkAttack PiEx ΓEx registryEx dpBadException
      (.undercut (.leaf l2)
        (.inst rWrapId [] [.leaf l1] [] [] .none) []) =
      .error (.R11 .root [] .undercut
        (.exceptionInstantiation rWrapId apQVar)) := by rfl

theorem check_undercut_missing_exception :
    checkAttack PiEx ΓEx registryEx dpRebut
      (.undercut (.leaf l2)
        (.inst rWrapId [] [.leaf l1] [] [] .none) []) =
      .error (.R11 .root [] .undercut
        (.missingException rWrapId)) := by rfl

theorem check_undercut_exception_mismatch :
    checkAttack PiEx ΓEx registryEx dpPos
      (.undercut (.leaf l1)
        (.inst rWrapId [] [.leaf l1] [] [] .none) []) =
      .error (.R11 .root [] .undercut
        (.exceptionMismatch rWrapId pA pB)) := by rfl

def lAbsent : LeafId := ⟨"absent-target-leaf"⟩

theorem check_undermine_undeclared_leaf :
    checkAttack PiEx ΓEx registryEx dpPos
      (.undermine (.leaf l1) (.leaf lAbsent) []) =
      .error (.R11 .root [] .undermine (.missingTargetLeaf lAbsent)) := by
  rfl

def badSource : SupportTerm := .leaf ⟨"missing-source"⟩

theorem check_attack_source_failure_rebut :
    checkAttack PiEx ΓEx registryEx dpRebut
      (.rebut badSource absentTarget) =
      .error (.R1 .root (.missingLeaf ⟨"missing-source"⟩)) := by rfl

theorem check_attack_source_failure_undercut :
    checkAttack PiEx ΓEx registryEx dpPos
      (.undercut badSource (.leaf l1) [.prem 99]) =
      .error (.R1 .root (.missingLeaf ⟨"missing-source"⟩)) := by rfl

theorem check_attack_source_failure_undermine :
    checkAttack PiEx ΓEx registryEx dpPos
      (.undermine badSource (.leaf lAbsent) []) =
      .error (.R1 .root (.missingLeaf ⟨"missing-source"⟩)) := by rfl

/-! ### §8 subargument closure, concretely -/

/-- The wrapper argument: a complete instance built on the leaf `l1`. -/
def vWrap : SupportTerm := .inst rWrapId [] [.leaf l1] [] [] .none

theorem sideWrap : InstSide id PiEx certOkNone rWrapId [] ruleWrap [.leaf l1] [] []
    .none [pA] [pA] [[]] [] [] pB where
  rule := by simp [PiEx, rMixId, rWrapId]
  θNodup := by simp
  θDom := by simp [ruleWrap]
  prems := by decide
  concl := by decide
  lenAs := rfl
  lenCs := rfl
  lenOs := rfl
  premEq := by
    intro i A B hA hB
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hA hB
      subst hA; subst hB
      exact equiv_refl id pA
    | succ j => simp at hA
  lenDCs := rfl
  lenDOs := rfl
  ans := by intro j q w A hD _; simp at hD
  qNodup := by simp [questionNames, ruleWrap]
  dNodup := by simp
  hNodup := by simp
  cover := by intro qd hqd; simp [ruleWrap] at hqd
  disj := by intro n hn; simp at hn
  keysD := by intro n hn; simp at hn
  keysH := by intro n hn; simp at hn
  strictNoQ := by intro h; simp [ruleWrap] at h
  assur := .defeasible rfl

theorem vWrap_typed : HasSupport id PiEx ΓEx certOkNone vWrap pB [] :=
  (by decide :
      collectObligations [[]] [] ruleWrap [] = []) ▸
    HasSupport.inst sideWrap
      (by
        intro i w A O hw hA hO
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hw hA hO
          subst hw; subst hA; subst hO
          exact .leaf (by decide)
        | succ j => simp at hw)
      no_dis

/-- The attack: `leaf l2` (concluding `pB`) undermines the declared argument
`leaf l1` at its root — `pB` is a declared contrary of `pA`. -/
def kAtk : Attack.Attack := .undermine (.leaf l2) (.leaf l1) []

/-! ### Supporting terms for the decidable-closure fixtures (Task 1)

Small closed terms exercising every branch of `containsB`/`attackClosureB`,
including the off-`DisNodup`-domain divergence between `containsB` and
`Contains` (a duplicate discharge key). -/

/-- A discharge-only instance: `l1` discharges question `q1`. Exercises the
`containsBDis` recursion (`containsB_discharge_hit`). -/
def vDis : SupportTerm := .inst rWrapId [] [] [(q1, .leaf l1)] [] .none

/-- A **duplicate discharge key** instance — `q1` maps to both `l1` and `l2`.
This is *not* `DisNodup`, so `containsB` (which scans every discharge branch)
and `Contains` (positional, where `lookupDis` returns the FIRST match only)
diverge on the query `.leaf l2`. -/
def vDup : SupportTerm :=
  .inst rWrapId [] [] [(q1, .leaf l1), (q1, .leaf l2)] [] .none

/-- A rebut whose attacked occurrence is the whole target term. -/
def kReb : Attack.Attack := .rebut (.leaf l2) vWrap

/-- An undermine descending to `vWrap`'s premise `.leaf l1` at `[.prem 0]`. -/
def kPos : Attack.Attack := .undermine (.leaf l2) vWrap [.prem 0]

/-- An undermine with an out-of-range premise index — `subterm` is `none`. -/
def kBadPos : Attack.Attack := .undermine (.leaf l2) vWrap [.prem 9]

def dpEx : Attack.DefeatPolicy := ⟨[(apB, apA)], []⟩

theorem kAtk_typed :
    Attack.HasAttack id PiEx ΓEx certOkNone dpEx kAtk :=
  .undermine (.leaf (by decide)) rfl (by decide)
    ⟨(apB, apA), by simp [dpEx], [], pB, pA, by decide, by decide,
      equiv_refl id pB, equiv_refl id pA⟩

/-- The program: attacker, attacked leaf argument, and a distinct wrapper
argument containing the attacked occurrence. -/
def PExCheck :=
  checkProgram PiEx ΓEx registryEx dpEx
    [.leaf l2, .leaf l1, vWrap] [kAtk]

theorem PExCheck_success : PExCheck.isOk = true := by decide

def PEx : CheckedProgram id PiEx ΓEx (certOkOf registryEx) dpEx :=
  PExCheck.toOption.get (by decide)

theorem PExCheck_ok : PExCheck = .ok PEx := by
  cases h : PExCheck with
  | error e =>
      have hs := PExCheck_success
      rw [h] at hs
      contradiction
  | ok program =>
      have hopt : PExCheck.toOption = some program :=
        congrArg Except.toOption h
      have hp : PEx = program := by
        unfold PEx
        apply Option.get_of_eq_some
        exact hopt
      rw [hp]

@[simp] theorem PEx_args :
    PEx.args = [.leaf l2, .leaf l1, vWrap] :=
  (checkProgram_sound PExCheck_ok).1

@[simp] theorem PEx_atts : PEx.atts = [kAtk] :=
  (checkProgram_sound PExCheck_ok).2.1

/-! ### Proof-bearing program checker matrix -/

/-- Equality descends through nested premise and discharge lists. -/
theorem supportTerm_nested_structural_equality :
    decide (tNest = tNest ∧ tI = tI) = true := by decide

def certNestedA : SupportTerm :=
  .inst rWrapId [] [tNest] [(q1, tI)] []
    (.cert ndId digestA slot0Cert)

def certNestedB : SupportTerm :=
  .inst rWrapId [] [tNest] [(q1, tI)] []
    (.cert ndId digestA slot1Cert)

/-- Structural identity is certificate-sensitive even beneath recursive lists. -/
theorem supportTerm_certificate_payload_distinct :
    certNestedA ≠ certNestedB := by decide

/-- A second ND proof of `pB` from `[pA]`: introduce a fresh `pA`, select the
fixed-theory `pB` at slot 2, then apply the resulting implication to slot 0. -/
def slot1WrappedCert : CertRef := ⟨.list
  [.atom "app",
    .list [.atom "lam", ndPWire,
      .list [.atom "hyp", .atom "2"]],
    .list [.atom "hyp", .atom "0"]]⟩

def certArgument (κ : CertRef) : SupportTerm :=
  .inst rCertId [] [.leaf l1] [] [] (.cert ndId digestA κ)

theorem registry_wrapped_certificate_accepts :
    certOkBOf registryEx ndId digestA slot1WrappedCert [pA] pB = true := by
  apply (certOkBOf_iff registryEx ndId digestA slot1WrappedCert [pA] pB).mpr
  change Lara.Strict.ndAccepts slot1WrappedCert
    ([Lara.Strict.ndEnc id pA] ++ [Lara.Strict.ndEnc id pB])
    (Lara.Strict.ndEnc id pB)
  refine ⟨.app (.lam ndP (.hyp 2)) (.hyp 0), ?_, ?_⟩
  · have h0 : Lara.ND.decodeNat "0" = some 0 := by
      change Lara.ND.decodeNat (Nat.repr 0) = some 0
      exact Lara.ND.decodeNat_repr 0
    have h2 : Lara.ND.decodeNat "2" = some 2 := by
      change Lara.ND.decodeNat (Nat.repr 2) = some 2
      exact Lara.ND.decodeNat_repr 2
    simp [slot1WrappedCert, ndPWire, ndP, Lara.Strict.ndEnc, pA,
      Lara.nf, Lara.nfTerms, Lara.ND.decodeCert,
      Lara.ND.decodeFormula, Lara.ND.Tag.parse, h0, h2]
  · apply Lara.ND.HasType.app
    · apply Lara.ND.HasType.lam
      exact Lara.ND.HasType.hyp rfl
    · exact Lara.ND.HasType.hyp rfl

theorem check_wrapped_certificate_success :
    inferSupport PiCert ΓEx registryEx .root
      (certArgument slot1WrappedCert) = .ok ⟨pB, []⟩ := by
  have hcert : certOkBOf registryEx ndId digestA slot1WrappedCert
      [Atom.atom "p" .nil] (Atom.atom "q" .nil) = true := by
    simpa [pA, pB] using registry_wrapped_certificate_accepts
  have hequiv : equiv id pA (Atom.atom "p" .nil) := by rfl
  simp [certArgument, inferSupport, inferSupportRaw, inferPremisesRaw,
    inferDischargesRaw, PiCert, ruleCert, ΓEx, requireB, instAPats,
    instAPat, instPats, Bind.bind, Except.bind, Pure.pure, Except.pure,
    apA, apB, pB, l1, substDomainB, atomsEquivB, questionNames, hequiv,
    collectObligations, unionAll, dedupQuestions, openMandatory,
    mandatoryNames, memB, knownAnswersOkB, strictNoQuestionB, assuranceOkB,
    hcert]

theorem check_program_empty :
    (checkProgram PiEx ΓEx registryEx dpEx [] []).isOk = true := by decide

theorem check_program_one_complete :
    (checkProgram PiEx ΓEx registryEx dpEx [.leaf l1] []).isOk = true := by
  decide

theorem check_program_full_PEx : PExCheck.isOk = true :=
  PExCheck_success

/-- Terms differing only in the opaque certificate payload remain two
declarations and are both accepted when both certificates replay. -/
theorem check_program_certificate_payload_distinct :
    (checkProgram PiCert ΓEx registryEx ⟨[], []⟩
      [certArgument slot1Cert, certArgument slot1WrappedCert] []).isOk =
        true := by
  obtain ⟨program, hprogram⟩ := checkProgram_complete
    (args := [certArgument slot1Cert, certArgument slot1WrappedCert])
    (atts := []) (dp := ⟨[], []⟩) (by decide)
    (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact ⟨pB, inferSupport_sound check_strict_cert_success⟩
      · exact ⟨pB, inferSupport_sound check_wrapped_certificate_success⟩)
    (by simp) (by simp) (by simp)
  rw [hprogram]
  rfl

theorem check_program_duplicate_first_pair :
    checkProgram PiEx ΓEx registryEx dpEx
      [.leaf l1, .leaf l2, .leaf l1, .leaf l2] [] =
      .error (.duplicateArgument 0 2) := by rfl

/-- Duplicate diagnostics are lexicographic by the first declaration index,
even when a later duplicate pair crosses an earlier adjacent pair. -/
theorem check_program_duplicate_crossing_first_pair :
    checkProgram PiEx ΓEx registryEx dpEx
      [.leaf l1, .leaf l2, .leaf l2, .leaf l1] [] =
      .error (.duplicateArgument 0 3) := by rfl

theorem check_program_incomplete_exact :
    checkProgram PiEx ΓEx registryEx dpEx [tMix] [] =
      .error (.incompleteArgument 0 [q1]) := by rfl

theorem check_program_incomplete_not_rejection_class :
    (ProgramError.incompleteArgument 0 [q1]).rejectClass = none := by rfl

theorem check_program_support_error_wrapped :
    checkProgram PiEx ΓEx registryEx dpEx [.leaf l1, badSource] [] =
      .error (.rejection (.argument 1)
        (.R1 .root (.missingLeaf ⟨"missing-source"⟩))) := by rfl

theorem check_program_first_argument_failure :
    checkProgram PiEx ΓEx registryEx dpEx
      [badSource, .leaf ⟨"another-missing"⟩] [] =
      .error (.rejection (.argument 0)
        (.R1 .root (.missingLeaf ⟨"missing-source"⟩))) := by rfl

theorem check_program_undeclared_source :
    checkProgram PiEx ΓEx registryEx dpEx [.leaf l1]
      [.undermine (.leaf l2) (.leaf l1) []] =
      .error (.rejection (.attack 0)
        (.R1 .root (.undeclaredAttackSource (.leaf l2)))) := by rfl

theorem check_program_undeclared_target :
    checkProgram PiEx ΓEx registryEx dpEx [.leaf l2] [kAtk] =
      .error (.rejection (.attack 0)
        (.R1 .root (.undeclaredAttackTarget (.leaf l1)))) := by rfl

theorem check_program_endpoint_reject_classes :
    (ProgramError.rejection (.attack 0)
      (.R1 .root (.undeclaredAttackSource (.leaf l2)))).rejectClass =
        some .R1 ∧
    (ProgramError.rejection (.attack 0)
      (.R1 .root (.undeclaredAttackTarget (.leaf l1)))).rejectClass =
        some .R1 := by decide

theorem check_program_rebut_error_wrapped :
    checkProgram PiEx ΓEx registryEx dpEx [.leaf l2, .leaf l1]
      [.rebut (.leaf l2) (.leaf l1)] =
      .error (.rejection (.attack 0)
        (.R10 .root [] .rebut
          (.wrongOccurrenceKind .rule .leaf))) := by rfl

theorem check_program_undercut_error_wrapped :
    checkProgram PiEx ΓEx registryEx dpEx [.leaf l2, .leaf l1]
      [.undercut (.leaf l2) (.leaf l1) []] =
      .error (.rejection (.attack 0)
        (.R10 .root [] .undercut
          (.wrongOccurrenceKind .rule .leaf))) := by rfl

theorem check_program_undermine_error_wrapped :
    checkProgram PiEx ΓEx registryEx dpEx [.leaf l2, vWrap]
      [.undermine (.leaf l2) vWrap []] =
      .error (.rejection (.attack 0)
        (.R10 .root [] .undermine
          (.wrongOccurrenceKind .leaf .rule))) := by rfl

theorem check_program_first_attack_failure :
    checkProgram PiEx ΓEx registryEx dpEx [.leaf l2, .leaf l1]
      [.rebut (.leaf l2) (.leaf l1),
        .undermine (.leaf l1) (.leaf l2) []] =
      .error (.rejection (.attack 0)
        (.R10 .root [] .rebut
          (.wrongOccurrenceKind .rule .leaf))) := by rfl

/-- Repeated attacks from one source traverse the retained source cache. -/
theorem check_program_many_attacks_one_source :
    (checkProgram PiEx ΓEx registryEx dpEx
      [.leaf l2, .leaf l1, vWrap] [kAtk, kAtk, kAtk]).isOk = true := by
  decide

/-- **Direct edge:** the attack's own declared target receives the edge. -/
theorem closure_edge_direct : Edge PEx (.leaf l2) (.leaf l1) :=
  ⟨by simp, by simp, kAtk, by simp, rfl,
    .leaf l1, rfl, contains_refl _⟩

/-- **Closure edge:** the wrapper argument — a *different* declared term
containing the attacked occurrence at `[.prem 0]` — also receives the edge.
This is the strict-superset behavior of subargument closure. -/
theorem closure_edge_wrapper : Edge PEx (.leaf l2) vWrap :=
  ⟨by simp, by simp, kAtk, by simp, rfl,
    .leaf l1, rfl, ⟨[.prem 0], by simp [vWrap, Attack.subterm]⟩⟩

/-! ### Decidable structural closure (`containsB`/`attackClosureB`, Task 1)

Branch-coverage fixtures for the total Boolean occurrence and closure
predicates, including the guarded-domain divergence from `Contains`. -/

theorem containsB_wrapper_leaf :
    Compile.containsB vWrap (.leaf l1) = true := by decide

theorem containsB_leaf_unrelated :
    Compile.containsB (.leaf l2) (.leaf l1) = false := by decide

theorem attackClosureB_direct :
    Compile.attackClosureB kAtk (.leaf l1) = true := by decide

theorem attackClosureB_wrapper :
    Compile.attackClosureB kAtk vWrap = true := by decide

/-- `containsB`: the `inst` self-equal true branch. -/
theorem containsB_inst_self : Compile.containsB vWrap vWrap = true := by decide

/-- `containsB`: positive discharge containment (exercises `containsBDis`). -/
theorem containsB_discharge_hit :
    Compile.containsB vDis (.leaf l1) = true := by decide

/-- `containsB` vs `Contains` DIVERGE off the well-formed (`DisNodup`) domain:
`vDup` scans both discharge branches, so `containsB` finds `.leaf l2`, but the
positional `Contains` cannot — `lookupDis` returns only the FIRST `q1` match
(`.leaf l1`). This is the shadowing counterexample the `DisNodup` guard on
`containsB_iff` rules out. -/
theorem containsB_dupkey_true :
    Compile.containsB vDup (.leaf l2) = true := by decide

theorem containsB_dupkey_not_contains :
    ¬ Compile.Contains vDup (.leaf l2) := by
  rintro ⟨π, hπ⟩
  cases π with
  | nil => simp [Attack.subterm, vDup, l1, l2] at hπ
  | cons e rest =>
    cases e with
    | prem i =>
      -- `vDup` has empty premise list, so `ws[i]? = none`.
      simp [Attack.subterm, vDup] at hπ
    | ques q =>
      -- `lookupDis` returns the FIRST `q1` match (`.leaf l1`); `q ≠ q1` is none.
      simp only [Attack.subterm, vDup] at hπ
      by_cases hq : q1 = q
      · subst hq
        simp only [Attack.lookupDis, if_pos] at hπ
        -- descended into `.leaf l1`, which can never reach `.leaf l2`.
        cases rest with
        | nil => simp [Attack.subterm, l1, l2] at hπ
        | cons e' rest' => simp [Attack.subterm] at hπ
      · simp [Attack.lookupDis, hq] at hπ

/-- `vDup` genuinely lies OFF the `DisNodup` domain: its discharge keys are
`[q1, q1]`, not `Nodup`. This pins as a theorem the "off-domain" premise that
`containsB_dupkey_true`/`containsB_dupkey_not_contains` rest on — the divergence
is a guarded-out case, not a `containsB`/`Contains` agreement bug. -/
theorem vDup_not_disNodup : ¬ Compile.DisNodup vDup := by
  simp [Compile.DisNodup, vDup]

/-- `attackClosureB`: the `.rebut` branch (occurrence IS the whole target). -/
theorem attackClosureB_rebut :
    Compile.attackClosureB kReb vWrap = true := by decide

/-- `attackClosureB`: positional `π ≠ []` some-case (descends into `vWrap`). -/
theorem attackClosureB_positional :
    Compile.attackClosureB kPos (.leaf l1) = true := by decide

/-- `attackClosureB`: out-of-position none→false case. -/
theorem attackClosureB_badpos :
    Compile.attackClosureB kBadPos (.leaf l1) = false := by decide

/-- **No spurious edge:** a term not containing the attacked occurrence gets
no edge. -/
theorem closure_no_edge_unrelated : ¬ Edge PEx (.leaf l2) (.leaf l2) := by
  rintro ⟨_, _, k, hk, hsrc, t, hocc, hcont⟩
  rw [PEx_atts] at hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  subst hk
  have ht : SupportTerm.leaf l1 = t := by
    simpa [kAtk, AttackOcc, Attack.subterm] using hocc
  subst ht
  obtain ⟨π, hπ⟩ := hcont
  cases π with
  | nil => simp [Attack.subterm, l1, l2] at hπ
  | cons e rest => cases e <;> simp [Attack.subterm] at hπ

/-- Exact characterization of the fixture's compiled relation: the one
declared attack produces precisely its direct and wrapper-closure edges. -/
theorem edge_fixture_iff (a b : SupportTerm) :
    Edge PEx a b ↔
      a = .leaf l2 ∧ (b = .leaf l1 ∨ b = vWrap) := by
  constructor
  · intro hE
    have hE' := hE
    obtain ⟨ha, hb, k, hk, hsrc, _, _, _⟩ := hE
    rw [PEx_atts] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    subst hk
    have ha' : a = .leaf l2 := by
      simpa [kAtk, Attack.Attack.source] using hsrc.symm
    rw [PEx_args] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | hb | hb
    · subst ha'; subst hb
      exact (closure_no_edge_unrelated hE').elim
    · exact ⟨ha', Or.inl hb⟩
    · exact ⟨ha', Or.inr hb⟩
  · rintro ⟨rfl, rfl | rfl⟩
    · exact closure_edge_direct
    · exact closure_edge_wrapper

/-- A concrete edge decider matching the two edges above
(attacker = index 0, target = 1, wrapper = 2). -/
def edgeBEx : Nat → Nat → Bool := fun i j => i == 0 && (j == 1 || j == 2)

/-- The concrete decider is not merely extensionally plausible: it decides
the source-level closure relation exactly, including the off-range boundary. -/
theorem edgeBEx_faithful : Faithful PEx edgeBEx where
  ranged := by
    intro i j hij
    simp only [edgeBEx, Bool.and_eq_true, beq_iff_eq,
      Bool.or_eq_true] at hij
    rcases hij with ⟨rfl, rfl | rfl⟩ <;> decide
  agrees := by
    intro i j a b ha hb
    have hi : i < 3 := by simpa using lt_of_getElem?_some ha
    have hj : j < 3 := by simpa using lt_of_getElem?_some hb
    obtain (rfl | rfl | rfl) : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    all_goals obtain (rfl | rfl | rfl) : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    all_goals rw [PEx_args] at ha hb
    all_goals simp only [List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at ha hb
    all_goals subst a
    all_goals subst b
    all_goals simp [edgeBEx, edge_fixture_iff, vWrap, l1, l2]

/-- **The checked-program edge decider on `PEx`.** `edgeB` reads the edges
directly off the checked program: index 0 (`.leaf l2`) attacks the direct target
1 (`.leaf l1`) and the wrapper 2 (`vWrap`); non-source rows and out-of-range
indices give no edge. -/
theorem checked_edge_fixture :
    Compile.edgeB PEx 0 1 = true ∧
    Compile.edgeB PEx 0 2 = true ∧
    Compile.edgeB PEx 1 1 = false ∧
    Compile.edgeB PEx 3 1 = false ∧
    Compile.edgeB PEx 0 3 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Compile.edgeB, PEx_args, PEx_atts, kAtk, List.any_cons,
      List.any_nil, Compile.attackClosureB, Attack.subterm, Compile.containsB,
      vWrap, l1, l2, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil] <;> decide

/-- The checked decider is faithful — a corollary of the general
`edgeB_faithful`, exercised on the running example. -/
theorem checked_edge_fixture_faithful :
    Compile.Faithful PEx (Compile.edgeB PEx) :=
  Compile.edgeB_faithful PEx

/-- **`edgeB PEx` and the hand-written `edgeBEx` decide the same edges.** The
checker-built decider extensionally matches the concrete oracle used above, so
the regression carries over. -/
theorem edgeB_PEx_eq_edgeBEx : Compile.edgeB PEx = edgeBEx := by
  funext i j
  rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;>
    simp only [Compile.edgeB, edgeBEx, PEx_args, PEx_atts, kAtk, List.any_cons,
      List.any_nil, Compile.attackClosureB, Attack.subterm, Compile.containsB,
      vWrap, l1, l2, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, Nat.reduceBEq] <;> rfl

/-- **Grounded verdict through the closure edges:** the attacker is `in`, the
attacked argument *and* the wrapper are `out`, and the wrapper's claim is
`defeated` purely via the closure edge — computed by the executable grounded
semantics over the compiled AF under the *checker-built* decider `edgeB PEx`. -/
theorem closure_grounded_verdict :
    Grounded.labelC (toAF PEx (Compile.edgeB PEx)) 0 = Grounded.Label.inn ∧
    Grounded.labelC (toAF PEx (Compile.edgeB PEx)) 1 = Grounded.Label.out ∧
    Grounded.labelC (toAF PEx (Compile.edgeB PEx)) 2 = Grounded.Label.out ∧
    Grounded.statusC (toAF PEx (Compile.edgeB PEx)) ⟨[2], []⟩
      = Grounded.Status.defeated := by
  rw [show Compile.edgeB PEx = edgeBEx from edgeB_PEx_eq_edgeBEx]; decide

/-- **Oracle-free compiled-AF status through `checkedAF`.** The wrapper AF is
`toAF PEx (edgeB PEx)`; the wrapper's claim is `defeated` computed by the
executable grounded semantics over it. -/
theorem checked_closure_status :
    Grounded.statusC (Compile.checkedAF PEx) ⟨[2], []⟩ =
      Grounded.Status.defeated := by
  rw [Compile.checkedAF,
    show Compile.edgeB PEx = edgeBEx from edgeB_PEx_eq_edgeBEx]; decide

/-- **Oracle-free source status witness.** `srcStatus_checked` supplies the
`Faithful` oracle constructively, so a source-level derivation exists for the
compiled `defeated` verdict with no oracle argument. -/
theorem checked_src_status_exists :
    ∃ s, Compile.SrcStatus PEx ⟨[2], []⟩ s :=
  ⟨Grounded.Status.defeated,
    Compile.srcStatus_checked PEx ⟨[2], []⟩⟩

/-! ### Public unit-acceptance boundary -/

/-- The finite policy whose derived lookup supplies every rule used by the
closed unit fixture.  All declarations are defeasible, so R12 is satisfied. -/
def unitPolicyEx : Policy.Policy :=
  { rules :=
      [ ⟨rMixId, ruleMix⟩
      , ⟨rWrapId, ruleWrap⟩
      , ⟨rPairId, rulePair⟩ ]
  , defeat := dpEx }

def rawUnitEx : Lara.Unit :=
  { policy := unitPolicyEx
  , args := [.leaf l2, .leaf l1]
  , atts := [kAtk] }

def rawUnitCheck :=
  checkUnit ΓEx registryEx rawUnitEx

/-- Matrix case 1: the canonical executable boundary accepts the complete
unit. -/
theorem check_unit_valid : rawUnitCheck.isOk = true := by decide

def acceptedUnitEx :
    Lara.Unit.CheckedUnit id ΓEx (certOkOf registryEx) :=
  rawUnitCheck.toOption.get (by decide)

theorem rawUnitCheck_ok : rawUnitCheck = .ok acceptedUnitEx := by
  cases h : rawUnitCheck with
  | error error =>
      have hs := check_unit_valid
      rw [h] at hs
      contradiction
  | ok accepted =>
      have hoption : rawUnitCheck.toOption = some accepted :=
        congrArg Except.toOption h
      have haccepted : acceptedUnitEx = accepted := by
        unfold acceptedUnitEx
        apply Option.get_of_eq_some
        exact hoption
      rw [haccepted]

/-- Matrix case 2: duplicate rule identifiers win first and retain both
declaration locations. -/
def duplicateRuleUnit : Lara.Unit :=
  { policy :=
      { rules := [⟨rMixId, ruleMix⟩, ⟨rMixId, ruleMix⟩]
      , defeat := dpEx }
  , args := []
  , atts := [] }

theorem check_unit_duplicate_rule_location :
    checkUnit ΓEx registryEx duplicateRuleUnit =
      .error (.duplicateRule ⟨rMixId, 0, 1⟩) := by rfl

/-- One strict rule whose conclusion touches the second side of the declared
contrary pair. -/
def r12PolicyEx : Policy.Policy :=
  { rules := [⟨rStrictId, ruleStrict⟩]
  , defeat := dpEx }

def r12UnitEx : Lara.Unit :=
  { policy := r12PolicyEx
  , args := []
  , atts := [] }

/-- Matrix case 3: R12 retains the offending rule and contrary declaration. -/
theorem check_unit_r12_location :
    checkUnit ΓEx registryEx r12UnitEx =
      .error (.policyViolation
        ⟨rStrictId, apA, (apB, apA)⟩) := by rfl

/-- Matrix case 4: the policy pass precedes the detailed program pass, even
when the raw argument declarations contain an immediate duplicate. -/
theorem check_unit_policy_before_duplicate_argument :
    checkUnit ΓEx registryEx
      { r12UnitEx with args := [.leaf l1, .leaf l1] } =
      .error (.policyViolation
        ⟨rStrictId, apA, (apB, apA)⟩) := by rfl

/-- AF-02 precedence pin: duplicate-rule validation wins even when the same
raw unit would also fail R12 and the program's duplicate-argument check. -/
theorem check_unit_duplicate_rule_before_policy_and_program :
    checkUnit ΓEx registryEx
      { policy :=
          { rules :=
              [⟨rStrictId, ruleStrict⟩, ⟨rStrictId, ruleStrict⟩]
          , defeat := dpEx }
      , args := [.leaf l1, .leaf l1]
      , atts := [] } =
      .error (.duplicateRule ⟨rStrictId, 0, 1⟩) := by rfl

/-- The unit error wrapper preserves the policy's frozen R12 class while
structural duplicate rules remain unclassified. -/
theorem unit_error_reject_classes :
    (UnitError.duplicateRule ⟨rMixId, 0, 1⟩).rejectClass = none ∧
    (UnitError.policyViolation
      ⟨rStrictId, apA, (apB, apA)⟩).rejectClass = some .R12 := by
  decide

/-- Task-6 UNT-05 pin: program-level argument duplication is wrapped without
changing its exact pair of locations. -/
theorem check_unit_duplicate_argument_wrapped :
    checkUnit ΓEx registryEx
      { policy := unitPolicyEx
      , args := [.leaf l1, .leaf l2, .leaf l1]
      , atts := [] } =
      .error (.program (.duplicateArgument 0 2)) := by rfl

/-- Matrix case 5: support diagnostics retain both their declaration location
and typed checker payload. -/
theorem check_unit_support_error_wrapped :
    checkUnit ΓEx registryEx
      { policy := unitPolicyEx
      , args := [.leaf l1, badSource]
      , atts := [] } =
      .error (.program (.rejection (.argument 1)
        (.R1 .root (.missingLeaf ⟨"missing-source"⟩)))) := by rfl

/-- Matrix case 6: typed-attack diagnostics are wrapped exactly. -/
theorem check_unit_typed_attack_error_wrapped :
    checkUnit ΓEx registryEx
      { policy := unitPolicyEx
      , args := [.leaf l2, .leaf l1]
      , atts := [.rebut (.leaf l2) (.leaf l1)] } =
      .error (.program (.rejection (.attack 0)
        (.R10 .root [] .rebut
          (.wrongOccurrenceKind .rule .leaf)))) := by rfl

/-- Matrix case 7: a fully typed program that omits a required conflict edge
reaches the final missing-conflict diagnostic. -/
theorem check_unit_missing_conflict_wrapped :
    checkUnit ΓEx registryEx
      { policy := unitPolicyEx
      , args := [.leaf l2, .leaf l1, vWrap]
      , atts := [] } =
      .error (.program
        (.missingConflict ⟨0, 1, pB, pA⟩)) := by rfl

/-- Matrix case 8: raw declarations, retained node order, and retained exact
conclusions all agree through the checked unit. -/
theorem checked_unit_retained_alignment :
    acceptedUnitEx.program.args = rawUnitEx.args ∧
    acceptedUnitEx.program.atts = rawUnitEx.atts ∧
    acceptedUnitEx.nodes.map (·.term) = acceptedUnitEx.program.args ∧
    acceptedUnitEx.nodes.map (·.conclusion) = [pB, pA] := by
  refine ⟨
    (checkUnit_sound rawUnitCheck_ok).2.2.2.1,
    (checkUnit_sound rawUnitCheck_ok).2.2.2.2.1,
    acceptedUnitEx.nodes_terms,
    ?_⟩
  decide

/-- Matrix case 9: the final executable claim status is obtained from the
program carried by the accepted unit, with no external edge oracle. -/
theorem checked_unit_final_status :
    Grounded.statusC (Compile.checkedAF acceptedUnitEx.program)
      ⟨[1], []⟩ = Grounded.Status.defeated := by
  decide

end Lara.Examples
