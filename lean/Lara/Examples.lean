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

namespace Lara.Examples

open Lara.Support Lara.Compile

/-! ### Fixture -/

def pA : Atom := .atom "p" .nil
def pB : Atom := .atom "q" .nil
def pC : Atom := .atom "s" .nil

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

def dpEx : Attack.DefeatPolicy := ⟨[(apB, apA)], []⟩

theorem kAtk_typed :
    Attack.HasAttack id PiEx ΓEx certOkNone dpEx kAtk :=
  .undermine (.leaf (by decide)) rfl (by decide)
    ⟨(apB, apA), by simp [dpEx], [], pB, pA, by decide, by decide,
      equiv_refl id pB, equiv_refl id pA⟩

/-- The program: attacker, attacked leaf argument, and a distinct wrapper
argument containing the attacked occurrence. -/
def PEx : CheckedProgram id PiEx ΓEx certOkNone dpEx where
  args := [.leaf l2, .leaf l1, vWrap]
  nodup := by simp [vWrap, l1, l2]
  complete := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨pB, .leaf (by decide)⟩
    · exact ⟨pA, .leaf (by decide)⟩
    · exact ⟨pB, vWrap_typed⟩
  atts := [kAtk]
  typed := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    subst hk
    exact kAtk_typed

/-- **Direct edge:** the attack's own declared target receives the edge. -/
theorem closure_edge_direct : Edge PEx (.leaf l2) (.leaf l1) :=
  ⟨by simp [PEx], by simp [PEx], kAtk, by simp [PEx], rfl,
    .leaf l1, rfl, contains_refl _⟩

/-- **Closure edge:** the wrapper argument — a *different* declared term
containing the attacked occurrence at `[.prem 0]` — also receives the edge.
This is the strict-superset behavior of subargument closure. -/
theorem closure_edge_wrapper : Edge PEx (.leaf l2) vWrap :=
  ⟨by simp [PEx], by simp [PEx], kAtk, by simp [PEx], rfl,
    .leaf l1, rfl, ⟨[.prem 0], by simp [vWrap, Attack.subterm]⟩⟩

/-- **No spurious edge:** a term not containing the attacked occurrence gets
no edge. -/
theorem closure_no_edge_unrelated : ¬ Edge PEx (.leaf l2) (.leaf l2) := by
  rintro ⟨_, _, k, hk, hsrc, t, hocc, hcont⟩
  simp only [PEx, List.mem_cons, List.not_mem_nil, or_false] at hk
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
    simp only [PEx, List.mem_cons, List.not_mem_nil, or_false] at hk
    subst hk
    have ha' : a = .leaf l2 := by
      simpa [kAtk, Attack.Attack.source] using hsrc.symm
    simp only [PEx, List.mem_cons, List.not_mem_nil, or_false] at hb
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
    have hi : i < 3 := by simpa [PEx] using lt_of_getElem?_some ha
    have hj : j < 3 := by simpa [PEx] using lt_of_getElem?_some hb
    obtain (rfl | rfl | rfl) : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    all_goals obtain (rfl | rfl | rfl) : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    all_goals simp only [PEx, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at ha hb
    all_goals subst a
    all_goals subst b
    all_goals simp [edgeBEx, edge_fixture_iff, vWrap, l1, l2]

/-- **Grounded verdict through the closure edges:** the attacker is `in`, the
attacked argument *and* the wrapper are `out`, and the wrapper's claim is
`defeated` purely via the closure edge — computed by the executable grounded
semantics over the compiled AF under the concrete decider. -/
theorem closure_grounded_verdict :
    Grounded.labelC (toAF PEx edgeBEx) 0 = Grounded.Label.inn ∧
    Grounded.labelC (toAF PEx edgeBEx) 1 = Grounded.Label.out ∧
    Grounded.labelC (toAF PEx edgeBEx) 2 = Grounded.Label.out ∧
    Grounded.statusC (toAF PEx edgeBEx) ⟨[2], []⟩ = Grounded.Status.defeated := by
  decide

end Lara.Examples
