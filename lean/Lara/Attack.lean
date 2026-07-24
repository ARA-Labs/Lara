/-
Mechanized typed positional attacks (`Lara.Attack`) — the Lean port of the
v0.1-frozen attack judgment `Sigma; Pi; Gamma; R |- k : attacks(w, u@π)`
(spec §7.1, frozen in the M1 lock pass). Ports the figure the moment it froze,
per the mechanization discipline (CLAUDE.md).

What this file discharges, against the exact §7.1 figure:

* `attack_source_checked` — every typed attack has a checked source (§1
  guarantee 4, the "checked, not complete" design point: no `O_w = ∅`
  requirement here; completeness gates AF entry at compile time).
* `rebut_top_defeasible`, `undercut_pos_defeasible` — **strict occurrences are
  unattackable**: the rule at a rebutted root or an undercut position is
  defeasible. §7's load-bearing property, now an inversion theorem.
* `undercut_target_rule`, `undermine_target_leaf` — the position-kind
  partition: an undercut lands on a rule occurrence, an undermine on a leaf
  occurrence (rebut's root shape is carried in its index).
* `rebut_concl_coherent` — the locality design point: [A-Rebut] reads the
  target conclusion off the root instance without typing `u`; if `u` *is*
  typed, the contrary match is against its typed conclusion. Uses
  `hasSupport_unique`-style inversion, so local checking and global typing
  agree.

Deferred with the executable checker (recorded in §7.1): the attack decision
procedure (result 1) and compile-facing edge soundness (result 4, lands with
the `compile` relation — lock item 11).

Design notes:

* Positions are element lists consumed left-to-right; the spec's `π.i`/`π.q`
  right-extension is the same data read from the root. Premise indices are
  0-based here (`ws[i]?`), 1-based in the presentation syntax.
* The defeat-relevant policy content (`contrary` pairs, `exception`
  declarations, spec §4) rides in a `DefeatPolicy` alongside the rule lookup
  `Pi` — parameters carry exactly what the metatheory needs (the
  `Lara.Strict` convention).
* `ContraryMatch` is §4.1's implicitly-universally-quantified `contrary`
  declaration: one ground `rho` instantiates a declared pair to the two ground
  propositions, up to `≡` (§3.2).
-/

import Lara.Support

namespace Lara.Attack

open Lara.Support

/-! ### Positions (spec §7: `π ::= ε | π.i | π.q`) -/

inductive PosElem where
  | prem : Nat → PosElem
  | ques : QuestionId → PosElem
deriving DecidableEq

abbrev Pos := List PosElem

def lookupDis : List (QuestionId × SupportTerm) → QuestionId → Option SupportTerm
  | [], _ => none
  | (q', w) :: rest, q => if q' = q then some w else lookupDis rest q

/-- `u@π`: the subterm occurrence at `π`, partial (spec §7.1). -/
def subterm : SupportTerm → Pos → Option SupportTerm
  | u, [] => some u
  | .leaf _, _ :: _ => none
  | .inst _ _ ws _ _ _, .prem i :: π =>
    match ws[i]? with
    | some w => subterm w π
    | none => none
  | .inst _ _ _ D _ _, .ques q :: π =>
    match lookupDis D q with
    | some w => subterm w π
    | none => none

/-! ### Defeat-relevant policy content (spec §4) -/

/-- The `contrary`/`exception` declarations of the selected policy.
`exceptions` entries are keyed by rule id (`exception r : E`). -/
structure DefeatPolicy where
  contraries : List (APat × APat)
  exceptions : List (RuleId × APat)

/-- §4.1 contrary instantiation: some declared `contrary A B` and one ground
`rho` have `A rho ≡ p` and `B rho ≡ q`. -/
def ContraryMatch (canon : String → String) (dp : DefeatPolicy)
    (p q : Atom) : Prop :=
  ∃ ab ∈ dp.contraries, ∃ (ρ : Subst) (pa pb : Atom),
    instAPat ρ ab.1 = some pa ∧ instAPat ρ ab.2 = some pb ∧
    equiv canon pa p ∧ equiv canon pb q

/-! ### The attack judgment (spec §7.1, v0.1-frozen) -/

/-- `k ::= rebut w u | undercut w u@π | undermine w u@π`. -/
inductive Attack where
  | rebut     : SupportTerm → SupportTerm → Attack
  | undercut  : SupportTerm → SupportTerm → Pos → Attack
  | undermine : SupportTerm → SupportTerm → Pos → Attack

def Attack.source : Attack → SupportTerm
  | .rebut w _ => w
  | .undercut w _ _ => w
  | .undermine w _ _ => w

/-- The attacked declared argument `u` (the whole term the position addresses
into). -/
def Attack.target : Attack → SupportTerm
  | .rebut _ u => u
  | .undercut _ u _ => u
  | .undermine _ u _ => u

/-- The three §7.1 rules. The source premise is a full typing (checked, not
complete); target-side premises are occurrence-local (`Pi`/`Gamma` lookups),
never a typing of `u` — the locality design point. -/
inductive HasAttack (canon : String → String) (Pi : RuleId → Option Rule)
    (Gamma : LeafId → Option Atom)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop)
    (dp : DefeatPolicy) : Attack → Prop where
  | rebut {w : SupportTerm} {rn : RuleId} {θ : Subst}
      {ws : List SupportTerm} {D : List (QuestionId × SupportTerm)}
      {H : List QuestionId} {a : Assurance} {r : Rule} {Cw Cu : Atom}
      {Ow : List QuestionId}
      (hw : HasSupport canon Pi Gamma CertOk w Cw Ow)
      (hrule : Pi rn = some r)
      (hdef : r.mode = .defeasible)
      (hconcl : instAPat θ r.concl = some Cu)
      (hcon : ContraryMatch canon dp Cw Cu) :
      HasAttack canon Pi Gamma CertOk dp (.rebut w (.inst rn θ ws D H a))
  | undercut {w u : SupportTerm} {π : Pos} {rn : RuleId} {θ : Subst}
      {ws : List SupportTerm} {D : List (QuestionId × SupportTerm)}
      {H : List QuestionId} {a : Assurance} {r : Rule} {E : APat} {e Cw : Atom}
      {Ow : List QuestionId}
      (hw : HasSupport canon Pi Gamma CertOk w Cw Ow)
      (hocc : subterm u π = some (.inst rn θ ws D H a))
      (hrule : Pi rn = some r)
      (hdef : r.mode = .defeasible)
      (hexc : (rn, E) ∈ dp.exceptions)
      (hinst : instAPat θ E = some e)
      (heq : equiv canon Cw e) :
      HasAttack canon Pi Gamma CertOk dp (.undercut w u π)
  | undermine {w u : SupportTerm} {π : Pos} {l : LeafId} {pl Cw : Atom}
      {Ow : List QuestionId}
      (hw : HasSupport canon Pi Gamma CertOk w Cw Ow)
      (hocc : subterm u π = some (.leaf l))
      (hl : Gamma l = some pl)
      (hcon : ContraryMatch canon dp Cw pl) :
      HasAttack canon Pi Gamma CertOk dp (.undermine w u π)

/-! ### §1 guarantee 4: checked source -/

/-- Every typed attack's source term type-checks. (Nothing requires its
obligation set to be empty — completeness is the compile step's gate.) -/
theorem attack_source_checked {canon Pi Gamma CertOk dp} {k : Attack}
    (hk : HasAttack canon Pi Gamma CertOk dp k) :
    ∃ Cw Ow, HasSupport canon Pi Gamma CertOk k.source Cw Ow := by
  cases hk with
  | rebut hw _ _ _ _ => exact ⟨_, _, hw⟩
  | undercut hw _ _ _ _ _ _ => exact ⟨_, _, hw⟩
  | undermine hw _ _ _ => exact ⟨_, _, hw⟩

/-! ### Strict occurrences are unattackable (spec §7) -/

/-- The rule at a rebutted root is defeasible — a strict-topped instance
cannot be rebutted. -/
theorem rebut_top_defeasible {canon Pi Gamma CertOk dp}
    {w : SupportTerm} {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {a : Assurance}
    (hk : HasAttack canon Pi Gamma CertOk dp (.rebut w (.inst rn θ ws D H a)))
    {r : Rule} (hr : Pi rn = some r) : r.mode = .defeasible := by
  cases hk with
  | rebut hw hrule hdef hconcl hcon =>
    rw [Option.some.inj (hrule.symm.trans hr)] at hdef
    exact hdef

/-- The rule at an undercut position is defeasible — a strict occurrence
cannot be undercut. Together with `rebut_top_defeasible`: strict inferences
are unattackable (ASPIC+, spec §7). -/
theorem undercut_pos_defeasible {canon Pi Gamma CertOk dp}
    {w u : SupportTerm} {π : Pos}
    (hk : HasAttack canon Pi Gamma CertOk dp (.undercut w u π))
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {a : Assurance}
    (hocc : subterm u π = some (.inst rn θ ws D H a))
    {r : Rule} (hr : Pi rn = some r) : r.mode = .defeasible := by
  cases hk with
  | undercut hw hocc' hrule hdef hexc hinst heq =>
    rw [hocc] at hocc'
    have hinj := Option.some.inj hocc'
    injection hinj with hrn hθ hws hD hH ha
    subst hrn
    rw [Option.some.inj (hrule.symm.trans hr)] at hdef
    exact hdef

/-! ### The position-kind partition (spec §7: three attacks, three positions) -/

/-- An undercut's target occurrence is a defeasible rule instance. -/
theorem undercut_target_rule {canon Pi Gamma CertOk dp}
    {w u : SupportTerm} {π : Pos}
    (hk : HasAttack canon Pi Gamma CertOk dp (.undercut w u π)) :
    ∃ rn θ ws D H a r, subterm u π = some (.inst rn θ ws D H a) ∧
      Pi rn = some r ∧ r.mode = .defeasible := by
  cases hk with
  | undercut hw hocc hrule hdef hexc hinst heq =>
    exact ⟨_, _, _, _, _, _, _, hocc, hrule, hdef⟩

/-- An undermine's target occurrence is a declared leaf. -/
theorem undermine_target_leaf {canon Pi Gamma CertOk dp}
    {w u : SupportTerm} {π : Pos}
    (hk : HasAttack canon Pi Gamma CertOk dp (.undermine w u π)) :
    ∃ l pl, subterm u π = some (.leaf l) ∧ Gamma l = some pl := by
  cases hk with
  | undermine hw hocc hl hcon => exact ⟨_, _, hocc, hl⟩

/-! ### Locality is coherent with global typing -/

/-- [A-Rebut] reads the target conclusion off the root instance without
typing `u`. If `u` *is* typed, that local read-off agrees: the contrary match
holds against `u`'s typed conclusion. Local attack checking and global
support typing cannot disagree. -/
theorem rebut_concl_coherent {canon Pi Gamma CertOk dp}
    {w u : SupportTerm}
    (hk : HasAttack canon Pi Gamma CertOk dp (.rebut w u))
    {Cu : Atom} {Ou : List QuestionId}
    (hu : HasSupport canon Pi Gamma CertOk u Cu Ou) :
    ∃ Cw Ow, HasSupport canon Pi Gamma CertOk w Cw Ow ∧
      ContraryMatch canon dp Cw Cu := by
  cases hk with
  | @rebut _ _ _ _ _ _ _ r Cw₀ Cu₀ Ow₀ hw hrule hdef hconcl hcon =>
    cases hu with
    | @inst _ _ _ _ _ _ r' As' Cs' Os' DCs' DOs' _ hside' _ _ =>
      have hrr : r' = r := Option.some.inj (hside'.rule.symm.trans hrule)
      rw [hrr] at hside'
      have hCu : Cu₀ = Cu := Option.some.inj (hconcl.symm.trans hside'.concl)
      exact ⟨Cw₀, Ow₀, hw, hCu ▸ hcon⟩

end Lara.Attack
