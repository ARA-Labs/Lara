/-
Direct surface observation and coherence with checked compilation.

The direct framework reads only the retained surface carrier: its argument
declaration order, lowered argument rows classified by their core support
typing into complete arguments and located holes, and resolved surface
attacks.  It is therefore available before framework compilation.  The
accepted surface derivation and unit-check result then prove that this
independently constructed framework agrees with the compiled core on its
carrier and attacks, and that the surface claim map reports exactly the
checked cache's incomplete alternatives.
-/

import Lara.Surface.Correctness
import Lara.Observation

namespace Lara.Surface

open Lara
open Lara.Grounded
open Lara.Semantics

variable {canon : String → String}

/-! ### Direct surface framework and claim -/

/-- The direct complete-argument list: the retained declarations whose core
support typing has an empty obligation set, in declaration order (spec §4.4).
Located holes are not AF nodes, so node identity is a position in this list,
never a raw declaration position: a leading hole cannot become node zero. -/
def directArgs (env : Env canon) (output : Elaborated canon) :
    List Support.SupportTerm :=
  Check.completeArgs output.unit.policy.ruleLookup output.gamma env.registry
    output.unit.args

/-- The direct AF-node-to-declaration map: the positions of the complete
retained declarations. -/
def directNodeDecls (env : Env canon) (output : Elaborated canon) : List Nat :=
  Check.completeDecls output.unit.policy.ruleLookup output.gamma env.registry
    output.unit.args

/-- The direct located-hole positions among the retained declarations. -/
def directHoleDecls (env : Env canon) (output : Elaborated canon) : List Nat :=
  Check.holeDecls output.unit.policy.ruleLookup output.gamma env.registry
    output.unit.args

/-- The surface attack decision at two direct node positions. It consumes the
resolved surface attacks directly; both endpoints index the complete-argument
list. -/
def directAttack (env : Env canon) (output : Elaborated canon) (i j : Nat) :
    Bool :=
  match (directArgs env output)[i]?, (directArgs env output)[j]? with
  | some source, some target =>
      Compile.coveredB output.resolvedAttacks source target
  | _, _ => false

/-- The AF exposed by an accepted surface derivation before framework
compilation. Node identity is the position in the direct complete-argument
list. -/
def directAF {env : Env canon} {input : Input} {output : Elaborated canon}
    (_h : Checks env input output) : AF where
  args := List.range (directArgs env output).length
  attack := directAttack env output

/-- Optional lookup shared only as a list primitive; the direct and core
ledgers supplied to it are independently defined. -/
def lookupClaim? (claims : List (Presentation.PropId × Claim))
    (claimId : Presentation.PropId) : Option Claim :=
  (claims.find? fun row => decide (row.1 = claimId)).map Prod.snd

/-- The core claim ledger: the retained claim alternatives classified by the
accepted unit's cached partition (`nodeDecls` and the located holes). -/
def coreClaims {Gamma : Support.LeafId → Option Atom}
    {CertOk : Support.BackendId → Support.Digest → Support.CertRef →
      List Atom → Atom → Prop}
    (output : Elaborated canon) (checked : Unit.CheckedUnit canon Gamma CertOk) :
    List (Presentation.PropId × Claim) :=
  claimsOf checked.nodeDecls (checked.holes.map (·.index))
    output.claimAlternatives

/-- Core-side optional lookup over the cache-classified claim ledger. -/
def coreClaim? {Gamma : Support.LeafId → Option Atom}
    {CertOk : Support.BackendId → Support.Digest → Support.CertRef →
      List Atom → Atom → Prop}
    (output : Elaborated canon) (checked : Unit.CheckedUnit canon Gamma CertOk)
    (claimId : Presentation.PropId) : Option Claim :=
  lookupClaim? (coreClaims output checked) claimId

/-- Independently recompute the surface claim ledger from the derivation's
semantic program and source reconstruction, classified by the direct
partition. No field reads `output.claimAlternatives` or a checked cache. -/
def directClaims (env : Env canon) (input : Input)
    (output : Elaborated canon) : List (Presentation.PropId × Claim) :=
  match reconstructArgs env output.semanticProgram input.policy
      output.semanticProgram.decls [] with
  | .error _ => []
  | .ok pairs =>
      claimsOf (directNodeDecls env output) (directHoleDecls env output)
        (claimAlternativesOf
          (keptReconstructed canon input.policy output.semanticProgram pairs)
          output.semanticProgram)

/-- Surface-side optional lookup. A missing declaration stays `none`; it is
not converted into an empty-support `gap` claim. -/
def directClaim {env : Env canon} {input : Input} {output : Elaborated canon}
    (_h : Checks env input output)
    (claimId : Presentation.PropId) : Option Claim :=
  lookupClaim? (directClaims env input output) claimId

/-- The direct carrier is exactly the index range of the direct
complete-argument list. -/
theorem directAF_args {env : Env canon} {input : Input} {output : Elaborated canon}
    (h : Checks env input output) :
    (directAF h).args = List.range (directArgs env output).length :=
  rfl

/-- Unfolding a direct edge exposes only the complete retained arguments and
the resolved surface attacks. -/
theorem directAF_attack_iff {env : Env canon} {input : Input}
    {output : Elaborated canon} (h : Checks env input output) (i j : Nat) :
    (directAF h).attack i j = true ↔
      (match (directArgs env output)[i]?, (directArgs env output)[j]? with
       | some source, some target =>
           Compile.coveredB output.resolvedAttacks source target = true
       | _, _ => False) := by
  cases hsource : (directArgs env output)[i]? <;>
    cases htarget : (directArgs env output)[j]? <;>
  simp [directAF, directAttack, hsource, htarget]

/-! ### Alignment supplied by an accepted surface derivation -/

/-- Every support index a classification produces is an AF node: it is a
position of the node-to-declaration map. -/
theorem claimsOf_support_lt {nodeDecls holeDecls : List Nat}
    {ledger : List (Presentation.PropId × List Nat)}
    {claimId : Presentation.PropId} {claim : Claim}
    (hclaim : (claimId, claim) ∈ claimsOf nodeDecls holeDecls ledger) :
    ∀ i ∈ claim.support, i < nodeDecls.length := by
  unfold claimsOf at hclaim
  obtain ⟨row, _, hrow⟩ := List.mem_map.mp hclaim
  cases hrow
  intro i hi
  obtain ⟨declaration, _, hidx⟩ := List.mem_filterMap.mp hi
  exact (List.idxOf?_eq_some_iff.mp hidx).1

private theorem zipIdx_pairwise_snd {α : Type} :
    ∀ (xs : List α) (k : Nat), (xs.zipIdx k).Pairwise (fun a b => a.2 < b.2)
  | [], _ => List.Pairwise.nil
  | x :: xs, k => by
      rw [List.zipIdx_cons, List.pairwise_cons]
      refine ⟨fun entry hentry => ?_, zipIdx_pairwise_snd xs (k + 1)⟩
      obtain ⟨y, i⟩ := entry
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (List.mem_zipIdx hentry).1

/-- Each claim's alternatives are strictly ascending declaration positions. -/
theorem claimAlternativesOf_sorted {pairs : List ReconstructedArgument}
    {program : Presentation.Program} {row : Presentation.PropId × List Nat}
    (hrow : row ∈ claimAlternativesOf pairs program) :
    row.2.Pairwise (· < ·) := by
  unfold claimAlternativesOf at hrow
  obtain ⟨claim, _, rfl⟩ := List.mem_map.mp hrow
  exact List.pairwise_map.mpr ((zipIdx_pairwise_snd pairs 0).filter _)

private theorem af_eq {F G : AF} (hargs : F.args = G.args)
    (hattack : F.attack = G.attack) : F = G := by
  cases F
  cases G
  simp_all

/-- The direct partition is the checked cache's partition on an accepted
unit: the core's node map and hole positions are determined by the support
classification of the retained declarations. -/
theorem directDecls_eq_checked {env : Env canon} {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked) :
    directNodeDecls env output = checked.nodeDecls ∧
      directHoleDecls env output = checked.holes.map (·.index) := by
  have hsound := Check.Unit.checkUnit_sound hchecked
  exact ⟨hsound.nodeDecls_eq.symm, hsound.holeIndices_eq.symm⟩

/-- The independently reconstructed and classified surface ledger agrees with
the cache-classified core ledger on an accepted derivation. -/
theorem directClaims_eq_coreClaims {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (h : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked) :
    directClaims env input output = coreClaims output checked := by
  rcases h.program with
    ⟨pairs, _, hprogram, _, _, _, _, _, hclaims, _⟩
  have hfold := reconstructArgs_complete hprogram
  obtain ⟨hnodes, hholes⟩ := directDecls_eq_checked hchecked
  simp [directClaims, coreClaims, hfold, hclaims, hnodes, hholes]

theorem directClaim_eq_coreClaim? {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (h : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked)
    (claimId : Presentation.PropId) :
    directClaim h claimId = coreClaim? output checked claimId := by
  simp [directClaim, coreClaim?, directClaims_eq_coreClaims h hchecked]

/-- Every argument supporting a direct claim is inside the direct carrier.
The bound is derived from `Checks` alone: support indices are positions of the
direct node map, which has one entry per complete retained argument. -/
theorem directClaim_support_bound {env : Env canon} {input : Input}
    {output : Elaborated canon} (h : Checks env input output)
    (claimId : Presentation.PropId) {claim : Claim}
    (hclaim : directClaim h claimId = some claim) :
    ∀ i ∈ claim.support, i ∈ (directAF h).args := by
  unfold directClaim lookupClaim? at hclaim
  cases hfind : (directClaims env input output).find?
      (fun row => decide (row.1 = claimId)) with
  | none => simp [hfind] at hclaim
  | some row =>
    simp only [hfind, Option.map_some, Option.some.injEq] at hclaim
    subst claim
    have hrow : row ∈ directClaims env input output :=
      List.mem_of_find?_eq_some hfind
    unfold directClaims at hrow
    split at hrow
    · simp at hrow
    · intro i hi
      have hlt := claimsOf_support_lt hrow i hi
      rw [directAF_args h, List.mem_range]
      rw [directNodeDecls, Check.completeDecls, Check.declPositions_length]
        at hlt
      exact hlt

/-- The direct surface framework and checked compilation are exactly equal.
The carrier is the complete-argument list, which is the accepted unit's AF
argument list; a direct edge from a complete source reads the raw resolved
attacks, which agree with the compiled live attacks from that source. -/
theorem direct_compiled_agree {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hsurface : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked) :
    directAF hsurface = Compile.checkedAF checked.program := by
  have hsound := Check.Unit.checkUnit_sound hchecked
  have hargs : directArgs env output = checked.program.args :=
    hsound.args_eq.symm
  apply af_eq
  · simp [directAF, Compile.checkedAF, Compile.toAF, hargs]
  · funext i j
    simp only [directAF, directAttack, Compile.checkedAF, Compile.toAF,
      Compile.edgeB, hargs]
    cases hi : checked.program.args[i]? with
    | none => rfl
    | some source =>
      cases checked.program.args[j]? with
      | none => rfl
      | some target =>
        simp only
        rw [hsound.atts_eq,
          Check.coveredB_liveAttacks (List.mem_of_getElem? hi),
          hsurface.unitAttacks]

/-! ### Surface/core hole coherence (D8, D10) -/

/-- The accepted unit's located-hole report over the retained ledger (D5):
every cached hole in checked declaration order, with the ArgId at its position
and its exact mandatory obligations. It is global: holes whose conclusion no
claim or query names are included. -/
def coreHoleReport {Gamma : Support.LeafId → Option Atom}
    {CertOk : Support.BackendId → Support.Digest → Support.CertRef →
      List Atom → Atom → Prop}
    (output : Elaborated canon) (checked : Unit.CheckedUnit canon Gamma CertOk) :
    List (Presentation.ArgId × List Support.QuestionId) :=
  checked.holes.filterMap fun hole =>
    (output.argIds[hole.index]?).map fun id => (id, hole.obligations)

/-- **The surface reports the core's incomplete alternatives.** On an
accepted derivation, every claim's alternatives — the retained arguments whose
authored conclusion supports it, after elaboration and admission — are
classified exactly by the checked cache:

* its holes are the global located holes sitting at its alternatives, in
  declaration order. The global list `checked.holes` also holds holes whose
  conclusion no claim names; a claim only selects among them;
* its support is the compact AF index of every alternative that is an AF node;
* each selected hole is the retained declaration at its position, carries the
  ArgId at that position — the ArgId its `coreHoleReport` row names — and its
  obligations are exactly the core's mandatory, transitive obligation set for
  that declaration.

Selection is by authored claim id, as for `support`. The conclusions of the
selected holes are `claimAlternatives_holes_sound`; the converse, under
distinct claim formals, is `claimAlternatives_holes_complete`.

There is no separate surface classification of holes: authored root questions,
optional ones included, decide nothing here. -/
theorem claimAlternatives_coherent {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hsurface : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked)
    {claimId : Presentation.PropId} {alternatives : List Nat}
    (hrow : (claimId, alternatives) ∈ output.claimAlternatives) :
    (classifyClaim checked.nodeDecls (checked.holes.map (·.index))
        alternatives).holes =
      (checked.holes.filter fun hole => decide (hole.index ∈ alternatives)).map
        (·.index) ∧
    (∀ n, n ∈ (classifyClaim checked.nodeDecls (checked.holes.map (·.index))
        alternatives).support ↔
      ∃ i ∈ alternatives, checked.nodeDecls[n]? = some i) ∧
    ∀ hole ∈ checked.holes, hole.index ∈ alternatives →
      output.unit.args[hole.index]? = some hole.term ∧
      (∃ id, output.argIds[hole.index]? = some id ∧
        (id, hole.obligations) ∈ coreHoleReport output checked) ∧
      ∀ C O, Support.HasSupport canon output.unit.policy.ruleLookup output.gamma
          (Support.certOkOf env.registry) hole.term C O →
        hole.conclusion = C ∧ hole.obligations = O := by
  have hsound := Check.Unit.checkUnit_sound hchecked
  rcases hsurface.program with
    ⟨pairs, _, _, _, _, _, hids, hargs, hclaims, _⟩
  have hsorted : alternatives.Pairwise (· < ·) := by
    rw [← hclaims] at hrow
    exact claimAlternativesOf_sorted hrow
  refine ⟨?_, ?_, ?_⟩
  · have hfilter : (checked.holes.filter fun hole =>
          decide (hole.index ∈ alternatives)).map (·.index) =
        (checked.holes.map (·.index)).filter fun i => decide (i ∈ alternatives) := by
      rw [List.filter_map]
      rfl
    rw [hfilter]
    apply Check.eq_of_pairwise_lt_of_mem_iff (hsorted.filter _)
      (hsound.partition.holes_sorted.filter _)
    intro i
    simp only [List.mem_filter, List.contains_iff_mem, decide_eq_true_eq]
    exact And.comm
  · intro n
    simp only [classifyClaim, List.mem_filterMap]
    constructor
    · rintro ⟨i, hi, hidx⟩
      obtain ⟨hn, hat, _⟩ := List.idxOf?_eq_some_iff.mp hidx
      exact ⟨i, hi, by rw [List.getElem?_eq_getElem hn, hat]⟩
    · rintro ⟨i, hi, hat⟩
      refine ⟨i, hi, ?_⟩
      obtain ⟨hn, heq⟩ := List.getElem?_eq_some_iff.mp hat
      exact List.idxOf?_eq_some_iff.mpr ⟨hn, heq, fun j hj hji => by
        have hlt := List.pairwise_iff_getElem.mp hsound.partition.nodeDecls_sorted
          j n (Nat.lt_trans hj hn) hn hj
        rw [hji, heq] at hlt
        exact Nat.lt_irrefl _ hlt⟩
  · intro hole hhole _
    have hat := hsound.partition.hole_decls hole hhole
    have hlen : output.argIds.length = output.unit.args.length := by
      rw [← hids, ← hargs, List.length_map, List.length_map]
    refine ⟨hat, ?_, fun C O hO =>
      (hsound.hole_reports_exact hhole hO).2⟩
    have hlt : hole.index < output.argIds.length := by
      rw [hlen]
      exact Support.lt_of_getElem?_some hat
    have hid := List.getElem?_eq_getElem hlt
    exact ⟨_, hid, List.mem_filterMap.mpr ⟨hole, hhole, by rw [hid]; rfl⟩⟩

/-! ### Conclusions of the selected holes

A surface claim selects its alternatives by authored claim id. A retained
`supports(c)` argument has passed the authored-conclusion check
(`ChecksAuthoredConclusion`), so its surface conclusion is equivalent to `c`'s
formal; lowering keeps the root rule and substitution, so a located hole's
cached conclusion is that surface conclusion. Hence every hole selected for `c`
concludes `c`'s formal. Conversely, conclusion equivalence selects nothing
more when every retained argument supports a formal-bearing claim and claim
formals are pairwise inequivalent; with shared formals, or with
derived-support or challenge roles, the id selection can miss alternatives the
core's conclusion-equivalence selection includes. -/

private theorem toSupportRuleId_injective {left right : Presentation.RuleId}
    (h : toSupportRuleId left = toSupportRuleId right) : left = right := by
  cases left
  cases right
  simp_all [toSupportRuleId]

private theorem lookupRuleDecl_toCoreRules {rules : List Presentation.Rule}
    {ruleId : Presentation.RuleId} {rule : Presentation.Rule}
    (h : FindsRule rules ruleId rule) :
    Lara.Policy.lookupRuleDecl
        (rules.map fun rule => ⟨toSupportRuleId rule.id, toCoreRule rule⟩)
        (toSupportRuleId ruleId) = some (toCoreRule rule) := by
  induction h with
  | here hid => simp [Lara.Policy.lookupRuleDecl, hid]
  | there hne _ ih =>
      simp only [List.map_cons, Lara.Policy.lookupRuleDecl]
      rw [if_neg fun heq => hne (toSupportRuleId_injective heq)]
      exact ih

/-- The lowered policy looks a found rule up as its lowering. -/
private theorem ruleLookup_toCorePolicy {policy : Presentation.Policy}
    {ruleId : Presentation.RuleId} {rule : Presentation.Rule}
    (h : FindsRule policy.rules ruleId rule) :
    (toCorePolicy policy).ruleLookup (toSupportRuleId ruleId) =
      some (toCoreRule rule) :=
  lookupRuleDecl_toCoreRules h

private theorem lookupSubst_lowered (theta : SurfaceSubst)
    (param : Presentation.Param) :
    Support.lookupSubst (theta.map fun pair => (toSupportParam pair.1, pair.2))
        (toSupportParam param) =
      lookupSurfaceSubst theta param := by
  induction theta with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨source, term⟩ := entry
      simp only [lookupSurfaceSubst] at ih ⊢
      by_cases hsame : source = param
      · subst hsame
        simp [Support.lookupSubst, List.findSome?]
      · have hlowered : toSupportParam source ≠ toSupportParam param := by
          intro heq
          apply hsame
          cases source
          cases param
          simp_all [toSupportParam]
        simp [Support.lookupSubst, List.findSome?, hsame, hlowered, ih]

mutual
  private theorem instPat_termToPat (θ : Support.Subst) :
      ∀ term : Term, Support.instPat θ (termToPat term) = some term
    | .num _ => rfl
    | .str _ => rfl
    | .con name terms => by
        simp [termToPat, Support.instPat, instPats_termsToPats θ terms]
  private theorem instPats_termsToPats (θ : Support.Subst) :
      ∀ terms : Terms, Support.instPats θ (termsToPats terms) = some terms
    | .nil => rfl
    | .cons term rest => by
        simp [termsToPats, Support.instPats, instPat_termToPat θ term,
          instPats_termsToPats θ rest]
end

mutual
  private theorem instPat_toCorePat (theta : SurfaceSubst) :
      ∀ pattern : Presentation.Pat,
        Support.instPat (theta.map fun pair => (toSupportParam pair.1, pair.2))
            (toCorePat pattern) =
          instantiateSurfacePat theta pattern
    | .var param => by
        simp [toCorePat, Support.instPat, instantiateSurfacePat,
          lookupSubst_lowered]
    | .lit term => by
        simp [toCorePat, instantiateSurfacePat, instPat_termToPat]
    | .con name patterns => by
        simp [toCorePat, Support.instPat, instantiateSurfacePat,
          instPats_toCorePats theta patterns]
  private theorem instPats_toCorePats (theta : SurfaceSubst) :
      ∀ patterns : Presentation.Pats,
        Support.instPats (theta.map fun pair => (toSupportParam pair.1, pair.2))
            (toCorePats patterns) =
          instantiateSurfacePats theta patterns
    | .nil => rfl
    | .cons pattern rest => by
        simp only [toCorePats, Support.instPats, instantiateSurfacePats,
          instPat_toCorePat theta pattern, instPats_toCorePats theta rest]
        cases instantiateSurfacePat theta pattern <;>
          cases instantiateSurfacePats theta rest <;> rfl
end

/-- Core instantiation of a lowered pattern under the lowered substitution is
surface instantiation. -/
private theorem instAPat_toCoreAtomPat (theta : SurfaceSubst)
    (pattern : Presentation.AtomPat) :
    Support.instAPat (theta.map fun pair => (toSupportParam pair.1, pair.2))
        (toCoreAtomPat pattern) =
      instantiateSurfaceAtom theta pattern := by
  simp [Support.instAPat, toCoreAtomPat, instantiateSurfaceAtom,
    instPats_toCorePats]

/-- **A retained hole concludes its argument's surface conclusion.** A typed
lowered argument with a nonempty obligation set is a rule instance, whose
cached conclusion is the surface rule conclusion under the surface
substitution; its authored role was checked against that conclusion. -/
private theorem checksArgument_hole_conclusion {env : Env canon}
    {program : Presentation.Program} {policy : Presentation.Policy}
    {priors : List PriorArgument} {argument : Presentation.Arg}
    {built : PriorArgument} {core : Support.SupportTerm}
    {Gamma : Support.LeafId → Option Atom}
    {CertOk : Support.BackendId → Support.Digest → Support.CertRef →
      List Atom → Atom → Prop}
    {C : Atom} {O : List Support.QuestionId}
    (hargument : ChecksArgument env program policy priors argument built core)
    (hsupport : Support.HasSupport canon (toCorePolicy policy).ruleLookup Gamma
      CertOk core C O)
    (hO : O ≠ []) :
    C = built.conclusion ∧
      ChecksAuthoredConclusion canon program built.conclusion argument.concl := by
  cases hargument with
  | explicit _ hconclusion hauthored hcertificate =>
      refine ⟨?_, hauthored⟩
      cases hconclusion with
      | leaf _ =>
          cases hcertificate
          cases hsupport
          exact absurd rfl hO
      | rule hrule hinst =>
          cases hcertificate with
          | rule _ _ _ _ =>
              obtain ⟨r, hr, hC⟩ := Support.hasSupport_inst_root hsupport
              rw [ruleLookup_toCorePolicy hrule, Option.some.injEq] at hr
              subst hr
              rw [toCoreRule, instAPat_toCoreAtomPat, hinst] at hC
              exact (Option.some.inj hC).symm
  | inferred hrule _ _ _ _ _ hconclusion hauthored hcertificate =>
      refine ⟨?_, hauthored⟩
      cases hcertificate with
      | rule _ _ _ _ =>
          obtain ⟨r, hr, hC⟩ := Support.hasSupport_inst_root hsupport
          rw [ruleLookup_toCorePolicy hrule, Option.some.injEq] at hr
          subst hr
          rw [toCoreRule, instAPat_toCoreAtomPat, hconclusion] at hC
          exact (Option.some.inj hC).symm

/-- Every reconstructed row comes from an argument declaration and carries its
argument derivation. -/
private theorem checksProgram_rows {env : Env canon}
    {program : Presentation.Program} {policy : Presentation.Policy}
    {declarations : List Presentation.Decl} {priors : List PriorArgument}
    {pairs : List ReconstructedArgument}
    (h : ChecksProgram env program policy declarations priors pairs) :
    ∀ pair ∈ pairs, Presentation.Decl.arg pair.argument ∈ declarations ∧
      ∃ priors', ChecksArgument env program policy priors' pair.argument
        pair.built pair.core := by
  induction h with
  | nil => simp
  | cons head _ ih =>
      intro pair hpair
      rcases List.mem_append.mp hpair with hnew | hrest
      · cases head with
        | arg hargument =>
            rw [List.mem_singleton] at hnew
            subst hnew
            exact ⟨List.mem_cons_self .., _, hargument⟩
        | leaf | claim | status | group | attack => simp at hnew
      · obtain ⟨hdeclared, hderived⟩ := ih pair hrest
        exact ⟨List.mem_cons_of_mem _ hdeclared, hderived⟩

/-- A ledger row is a declared claim's id, and its alternatives are the
positions of the rows whose authored conclusion supports that id. -/
private theorem mem_claimAlternativesOf {pairs : List ReconstructedArgument}
    {program : Presentation.Program} {claimId : Presentation.PropId}
    {alternatives : List Nat}
    (hrow : (claimId, alternatives) ∈ claimAlternativesOf pairs program) :
    (∃ formal, claimFormal? program claimId = some formal) ∧
      ∀ i, i ∈ alternatives ↔ ∃ pair, pairs[i]? = some pair ∧
        argSupportsClaim claimId pair.argument.concl = true := by
  unfold claimAlternativesOf at hrow
  obtain ⟨claim, hclaim, hrowEq⟩ := List.mem_map.mp hrow
  obtain ⟨declaration, hdeclaration, hselect⟩ := List.mem_filterMap.mp hclaim
  have hdecl : declaration = .claim claim := by
    cases declaration <;> simp_all
  subst hdecl
  simp only [Prod.mk.injEq] at hrowEq
  obtain ⟨hid, rfl⟩ := hrowEq
  subst hid
  refine ⟨?_, fun i => ?_⟩
  · have hsome : (claimFormal? program claim.id).isSome := by
      unfold claimFormal? claimFormalIn?
      exact List.findSome?_isSome_iff.mpr ⟨_, hdeclaration, by simp⟩
    exact Option.isSome_iff_exists.mp hsome
  · simp only [List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨⟨pair, j⟩, ⟨hzip, hsupports⟩, rfl⟩
      exact ⟨pair, List.mem_zipIdx_iff_getElem?.mp hzip, hsupports⟩
    · rintro ⟨pair, hat, hsupports⟩
      exact ⟨(pair, i), ⟨List.mem_zipIdx_iff_getElem?.mpr hat, hsupports⟩, rfl⟩

/-- The retained row at a located hole's position: its core term is the hole's
term, it is a reconstructed argument declaration, and the hole's cached
conclusion is its checked surface conclusion. -/
private theorem hole_row {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked)
    {pairs : List ReconstructedArgument}
    (hprogram : ChecksProgram env output.semanticProgram input.policy
      output.semanticProgram.decls [] pairs)
    (hargs : (keptReconstructed canon input.policy output.semanticProgram
      pairs).map (·.core) = output.unit.args)
    (hpolicy : toCorePolicy input.policy = output.unit.policy)
    {hole : Compile.CheckedHole canon checked.policy.ruleLookup output.gamma
      (Support.certOkOf env.registry)}
    (hhole : hole ∈ checked.holes) {pair : ReconstructedArgument}
    (hat : (keptReconstructed canon input.policy output.semanticProgram
      pairs)[hole.index]? = some pair) :
    Presentation.Decl.arg pair.argument ∈ output.semanticProgram.decls ∧
      ChecksAuthoredConclusion canon output.semanticProgram hole.conclusion
        pair.argument.concl := by
  have hsound := Check.Unit.checkUnit_sound hchecked
  have hterm : pair.core = hole.term := by
    have hdecl := hsound.partition.hole_decls hole hhole
    rw [← hargs, List.getElem?_map, hat, Option.map_some,
      Option.some.injEq] at hdecl
    exact hdecl
  have hmem : pair ∈ pairs :=
    (List.mem_filter.mp (List.mem_of_getElem? hat)).1
  obtain ⟨hdeclared, priors, hargument⟩ := checksProgram_rows hprogram pair hmem
  have hvalid : Support.HasSupport canon (toCorePolicy input.policy).ruleLookup
      output.gamma (Support.certOkOf env.registry) pair.core hole.conclusion
      hole.obligations := by
    rw [hpolicy, ← hsound.policy_eq, hterm]
    exact hole.valid
  obtain ⟨hconclusion, hauthored⟩ :=
    checksArgument_hole_conclusion hargument hvalid hole.nonempty
  rw [hconclusion]
  exact ⟨hdeclared, hauthored⟩

/-- **Selected holes conclude the claim's formal.** Every located hole a claim
selects concludes, up to `≡`, the formal of that claim. The premise excludes
the derived-support role `supportsDerived c`, which the authored-conclusion
check does not compare with a formal. -/
theorem claimAlternatives_holes_sound {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hsurface : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked)
    {claimId : Presentation.PropId} {alternatives : List Nat}
    (hrow : (claimId, alternatives) ∈ output.claimAlternatives)
    (hderived : ∀ argument,
      Presentation.Decl.arg argument ∈ output.semanticProgram.decls →
        argument.concl ≠ .supportsDerived claimId) :
    ∃ formal, claimFormal? output.semanticProgram claimId = some formal ∧
      ∀ hole ∈ checked.holes, hole.index ∈ alternatives →
        Lara.equiv canon hole.conclusion formal := by
  rcases hsurface.program with
    ⟨pairs, _, hprogram, _, _, _, _, hargs, hclaims, _⟩
  rw [← hclaims] at hrow
  obtain ⟨⟨formal, hformal⟩, hmem⟩ := mem_claimAlternativesOf hrow
  refine ⟨formal, hformal, fun hole hhole hindex => ?_⟩
  obtain ⟨pair, hat, hsupports⟩ := (hmem hole.index).mp hindex
  obtain ⟨hdeclared, hauthored⟩ := hole_row hchecked hprogram hargs
    hsurface.unitPolicy hhole hat
  cases hconcl : pair.argument.concl with
  | supportsClaim id =>
      rw [hconcl] at hsupports hauthored
      have hid : id = claimId := by simpa [argSupportsClaim] using hsupports
      subst hid
      cases hauthored with
      | supportsClaimKnown hclaim hequiv =>
          rw [hformal, Option.some.injEq] at hclaim
          subst hclaim
          exact hequiv
      | supportsClaimDerived hclaim =>
          rw [hformal] at hclaim
          cases hclaim
  | supportsDerived id =>
      rw [hconcl] at hsupports
      have hid : id = claimId := by simpa [argSupportsClaim] using hsupports
      exact absurd (hid ▸ hconcl) (hderived pair.argument hdeclared)
  | challenges _ =>
      rw [hconcl] at hsupports
      simp [argSupportsClaim] at hsupports

/-- **Conclusion selection adds nothing under distinct formals.** If every
retained argument declaration supports a claim that has a formal, and no other
claim's formal is equivalent to this claim's, then every located hole whose
cached conclusion is equivalent to the claim's formal is selected for the
claim. Without these premises a shared formal, a derived-support role or a
challenge role concluding the formal leaves a hole the core's
conclusion-equivalence selection would include. -/
theorem claimAlternatives_holes_complete {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hsurface : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked)
    {claimId : Presentation.PropId} {alternatives : List Nat}
    (hrow : (claimId, alternatives) ∈ output.claimAlternatives)
    (hroles : ∀ argument,
      Presentation.Decl.arg argument ∈ output.semanticProgram.decls →
        ∃ claim formal, argument.concl = .supportsClaim claim ∧
          claimFormal? output.semanticProgram claim = some formal)
    {formal : Atom}
    (hformal : claimFormal? output.semanticProgram claimId = some formal)
    (hdistinct : ∀ claim other,
      claimFormal? output.semanticProgram claim = some other →
        Lara.equiv canon other formal → claim = claimId) :
    ∀ hole ∈ checked.holes, Lara.equiv canon hole.conclusion formal →
      hole.index ∈ alternatives := by
  have hsound := Check.Unit.checkUnit_sound hchecked
  rcases hsurface.program with
    ⟨pairs, _, hprogram, _, _, _, _, hargs, hclaims, _⟩
  rw [← hclaims] at hrow
  obtain ⟨_, hmem⟩ := mem_claimAlternativesOf hrow
  intro hole hhole hequiv
  have hlt : hole.index <
      (keptReconstructed canon input.policy output.semanticProgram pairs).length := by
    have hdecl := hsound.partition.hole_decls hole hhole
    rw [← hargs] at hdecl
    simpa using Support.lt_of_getElem?_some hdecl
  have hat := List.getElem?_eq_getElem hlt
  obtain ⟨hdeclared, hauthored⟩ := hole_row hchecked hprogram hargs
    hsurface.unitPolicy hhole hat
  obtain ⟨claim, other, hconcl, hother⟩ := hroles _ hdeclared
  rw [hconcl] at hauthored
  cases hauthored with
  | supportsClaimKnown hclaim hclaimEquiv =>
      rw [hother, Option.some.injEq] at hclaim
      subst hclaim
      have hsame := hdistinct claim other hother
        (Lara.equiv_trans canon (Lara.equiv_symm canon hclaimEquiv) hequiv)
      subst hsame
      exact (hmem hole.index).mpr ⟨_, hat, by simp [hconcl, argSupportsClaim]⟩
  | supportsClaimDerived hclaim =>
      rw [hother] at hclaim
      cases hclaim

/-- On an accepted derivation the report drops no hole: it lists every cached
hole's obligations, in order. -/
theorem coreHoleReport_obligations {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hsurface : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked) :
    (coreHoleReport output checked).map Prod.snd =
      checked.holes.map (·.obligations) := by
  have hsound := Check.Unit.checkUnit_sound hchecked
  rcases hsurface.program with
    ⟨pairs, _, _, _, _, _, hids, hargs, _, _⟩
  have hlen : output.argIds.length = output.unit.args.length := by
    rw [← hids, ← hargs, List.length_map, List.length_map]
  have hall : ∀ hole ∈ checked.holes, ∃ id,
      output.argIds[hole.index]? = some id := by
    intro hole hhole
    have hlt : hole.index < output.argIds.length := by
      rw [hlen]
      exact Support.lt_of_getElem?_some (hsound.partition.hole_decls hole hhole)
    exact ⟨_, List.getElem?_eq_getElem hlt⟩
  unfold coreHoleReport
  generalize checked.holes = holes at hall ⊢
  induction holes with
  | nil => rfl
  | cons hole rest ih =>
    obtain ⟨id, hid⟩ := hall hole (List.mem_cons_self ..)
    simp only [List.filterMap_cons, hid, Option.map_some, List.map_cons]
    exact congrArg _ (ih fun h hh => hall h (List.mem_cons_of_mem _ hh))

/-! ### Semantics-parametric observation coherence -/

/-- Optional direct surface observation. Missing claims remain missing. -/
def observe (sem : ExtensionSemantics)
    {env : Env canon} {input : Input} {output : Elaborated canon}
    (h : Checks env input output) (claimId : Presentation.PropId) :
    Option ClaimObservation :=
  (directClaim h claimId).map (Semantics.observe sem (directAF h))

/-- Direct surface observation agrees with checked compilation for every
carrier-local extension semantics. -/
theorem observe_coherent (sem : ExtensionSemantics)
    (hext : Observation.AttackExtensional sem.spec)
    {env : Env canon} {input : Input} {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hsurface : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked)
    (claimId : Presentation.PropId) :
    Lara.Surface.observe sem hsurface claimId =
      (coreClaim? output checked claimId).map
        (Semantics.observe sem (Compile.checkedAF checked.program)) := by
  unfold Lara.Surface.observe
  rw [directClaim_eq_coreClaim? hsurface hchecked,
    direct_compiled_agree hsurface hchecked]

/-- Grounded observation coherence (`groundedSem.spec` is `LeastComplete`). -/
theorem observe_grounded_coherent {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hsurface : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked)
    (claimId : Presentation.PropId) :
    Lara.Surface.observe groundedSem hsurface claimId =
      (coreClaim? output checked claimId).map
        (Semantics.observe groundedSem (Compile.checkedAF checked.program)) :=
  observe_coherent groundedSem Observation.attackExtensional_leastComplete
    hsurface hchecked claimId

/-- Complete-semantics observation coherence. -/
theorem observe_complete_coherent {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hsurface : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked)
    (claimId : Presentation.PropId) :
    Lara.Surface.observe completeSem hsurface claimId =
      (coreClaim? output checked claimId).map
        (Semantics.observe completeSem (Compile.checkedAF checked.program)) :=
  observe_coherent completeSem Observation.attackExtensional_complete
    hsurface hchecked claimId

/-- Preferred-semantics observation coherence. -/
theorem observe_preferred_coherent {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hsurface : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked)
    (claimId : Presentation.PropId) :
    Lara.Surface.observe preferredSem hsurface claimId =
      (coreClaim? output checked claimId).map
        (Semantics.observe preferredSem (Compile.checkedAF checked.program)) :=
  observe_coherent preferredSem Observation.attackExtensional_preferred
    hsurface hchecked claimId

/-- Stable-semantics observation coherence, including `noExtension`. -/
theorem observe_stable_coherent {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hsurface : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked)
    (claimId : Presentation.PropId) :
    Lara.Surface.observe stableSem hsurface claimId =
      (coreClaim? output checked claimId).map
        (Semantics.observe stableSem (Compile.checkedAF checked.program)) :=
  observe_coherent stableSem Observation.attackExtensional_stable
    hsurface hchecked claimId

/-- Semi-stable-semantics observation coherence. -/
theorem observe_semiStable_coherent {env : Env canon} {input : Input}
    {output : Elaborated canon}
    {checked : Unit.CheckedUnit canon output.gamma
      (Support.certOkOf env.registry)}
    (hsurface : Checks env input output)
    (hchecked : Check.Unit.checkUnit output.gamma env.registry
      output.ground output.unit = .ok checked)
    (claimId : Presentation.PropId) :
    Lara.Surface.observe semiStableSem hsurface claimId =
      (coreClaim? output checked claimId).map
        (Semantics.observe semiStableSem (Compile.checkedAF checked.program)) :=
  observe_coherent semiStableSem Observation.attackExtensional_semiStable
    hsurface hchecked claimId

/-! ### The support premise is load-bearing -/

/-- A would-be direct claim whose sole support lies outside the retained
carrier used by the generic congruence counterexample. -/
def unboundedDirectClaim : Claim := Observation.claimJunkSupport

/-- The witness really violates the support premise: argument `7` is not in the
retained carrier `[0]`. -/
theorem unboundedDirectClaim_support_unaligned :
    ¬ (∀ i ∈ unboundedDirectClaim.support,
        i ∈ Observation.oneNoAttack.args) := by
  decide

/-- Dropping direct support alignment makes observation coherence false even
when the two frameworks have the same carrier and agree on every carrier edge. -/
theorem not_observe_coherent_of_unbounded_support :
    Semantics.observe groundedSem Observation.oneNoAttack unboundedDirectClaim ≠
      Semantics.observe groundedSem Observation.oneAttacksJunk unboundedDirectClaim :=
  Observation.not_observe_congr_of_unbounded_support

end Lara.Surface
