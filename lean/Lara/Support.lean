/-
Mechanized support-term typing (`Lara.Support`) — the Lean port of the
v0.1-frozen judgment `Sigma; Pi; Gamma; R |- w : supports(p) ▷ O` (spec §6.1,
frozen 2026-07-22 in the M1 lock pass). Per the mechanization discipline
(CLAUDE.md): the definition froze, so its metatheory lands now.

What this file discharges, against the exact §6.1 figure:

* **Result 3 (dependency accountability), both halves.** Leaf half —
  `leaves_declared`: every leaf constant of a typed term is declared in
  `Gamma`; "the reported leaf set equals `leaves(w)`" is definitional (the
  report *is* `leaves w`, spec §6). Certificate half — the `certDeps` layer
  at the end of this file over the `Backend.uses` report laws (obligation 4):
  every reported slot resolves to a typed `CertDep` (premise occurrence or
  digest-addressed theory entry — the Haskell `Dependency` split, nothing
  filtered); `cert_steps_accounted` (every certificate node's conclusion
  follows from just the reported entries of the full consulted context —
  selected premises and selected theory entries alike), the collection
  identity `mem_certDeps_step` / `certStep_deps_subset`, `certDeps_resolved`
  (premise entries resolve to the corresponding premise subterm of their own
  reporting node, up to `≡`), and `certDeps_theory_valid` (theory entries
  name genuine entries of the digest-resolved theory data).
* **Result 1 (decidability), uniqueness half** — `hasSupport_unique`: a term
  has at most one conclusion and obligation set. `Lara.Check.Support` supplies
  the executable checker; `Lara.Check.SupportProof` proves soundness and exact
  completeness against this relation.
* **Result 11 (support adequacy), relational layer** — `Supports` is `≡` on
  the unique conclusion; `supports_resp_equiv` shows it is `≡`-functional.
* The §6.1 accounting invariants as inversion lemmas: `strict_no_questions`
  (a strict instance carries no discharge map and no holes),
  `complete_mandatory_discharged` (`O = []` at an instance root forces every
  mandatory question into the discharge map), and `dh_partition` (the
  `D ⊎ H = questions(r)` cover/disjointness, extensionally).
* `certOkOf_strict_step`: the §6.1 `cert` assurance side condition composed
  with the abstract seam yields Theorem 1's consequence — §6 and §5 agree.

Design notes (same conventions as the sibling files):

* Domain identifiers and symbols are distinct newtypes (`RuleId`, `LeafId`,
  `QuestionId`, `VarId`, `PredSym`, `ConSym`, `BackendId`, `Digest`,
  `CertRef`) per the symbolic-core rule (CLAUDE.md): separate namespaces
  cannot be swapped silently; raw strings live only inside the wrappers,
  converted at the decode boundary. Instantiation unwraps `PredSym`/`ConSym`
  only when producing the already-frozen ground `Lara.Prop` representation.
* Contexts are functions (`Pi : RuleId → Option Rule`, `Gamma : LeafId →
  Option Atom`): they are checker *inputs*, not wire data, so totality via
  `Option` is the honest model. The wire substitution `theta` *is* data
  (spec §4.1: JSON carries it explicitly), so it is an association list; the
  §6.1 side condition `dom(theta) = {X1..Xm}` is carried exactly by the
  `InstSide.θDom`/`θNodup` fields against the rule's declared `params`.
* The `cert(beta, theory-digest, kappa)` assurance carries all three values:
  backend id, digest, and an *opaque* certificate reference — the payload is
  never inspected here (the factivity firewall, Theorem 3). Acceptance is the
  indexed predicate `CertOk β h κ As C`, gated per-rule by the `certifiers`
  allowlist (spec §4: an instance may use `cert(beta, h, ...)` only when
  `(beta@version, h)` appears in `certifiers`); `certOkOf` instantiates it
  from a backend-first registry: one fixed backend core per identity, whose
  inner resolver returns only the digest's theory data.
* Rule-instance children are indexed by `l[i]?` lookups rather than nested
  `Forall₂`-style premises, keeping every recursive occurrence directly under
  `∀`/`→` (strictly positive, clean induction principles). List-shape helper
  lemmas are proved by hand, self-contained (the `Lara/Grounded.lean` style).
-/

import Lara.Prop
import Lara.Strict

namespace Lara.Support

/-! ### Domain identifiers (symbolic core: one newtype per namespace) -/

/-- Inference-scheme (rule) identifier. -/
structure RuleId where
  name : String
deriving DecidableEq

/-- Evidence-leaf identifier. -/
structure LeafId where
  name : String
deriving DecidableEq

/-- Critical-question identifier. -/
structure QuestionId where
  name : String
deriving DecidableEq

/-- Rule-parameter (variable) identifier. -/
structure VarId where
  name : String
deriving DecidableEq

/-- Predicate symbol. Kept distinct from constructor symbols in the core AST. -/
structure PredSym where
  name : String
deriving DecidableEq

/-- Term-constructor symbol. Kept distinct from predicate symbols. -/
structure ConSym where
  name : String
deriving DecidableEq

/-- Strict-backend identifier (`beta`). -/
structure BackendId where
  name    : String
  version : Nat
deriving DecidableEq

/-- Theory digest (`h`), digest-addressed. -/
structure Digest where
  hash : String
deriving DecidableEq

/-! ### Patterns and substitutions (spec §4.1) -/

/- Rule-body patterns `P ::= X | k | k(P1, ..., Pn)`; mutual argument list as
in `Lara.Term`/`Terms`. -/
mutual
  inductive Pat where
    | var : VarId → Pat
    | num : String → Pat
    | str : String → Pat
    | con : ConSym → Pats → Pat
  inductive Pats where
    | nil  : Pats
    | cons : Pat → Pats → Pats
end
deriving instance DecidableEq for Pat, Pats

/-- An atom pattern `Apat ::= pred(P1, ..., Pn)`. -/
structure APat where
  pred : PredSym
  args : Pats
deriving DecidableEq

/-- The wire substitution: explicit, ground by construction (`Term` is ground). -/
abbrev Subst := List (VarId × Term)

def lookupSubst : Subst → VarId → Option Term
  | [], _ => none
  | (y, t) :: rest, x => if y = x then some t else lookupSubst rest x

/- Instantiation `P theta` — `none` iff a variable is unbound. The §6.1 side
condition `dom(theta) = {X1..Xm}` is NOT this success condition (which only
sees variables actually occurring in the instantiated pattern); it is the
`InstSide.θDom`/`θNodup` fields against the rule's declared `params`. -/
mutual
  def instPat (θ : Subst) : Pat → Option Term
    | .var x => lookupSubst θ x
    | .num s => some (.num s)
    | .str s => some (.str s)
    | .con k ps => (instPats θ ps).map (.con k.name)
  def instPats (θ : Subst) : Pats → Option Terms
    | .nil => some .nil
    | .cons p ps =>
      match instPat θ p, instPats θ ps with
      | some t, some ts => some (.cons t ts)
      | _, _ => none
end

/-- `Apat theta` as a ground atom. -/
def instAPat (θ : Subst) (ap : APat) : Option Atom :=
  (instPats θ ap.args).map (.atom ap.pred.name)

def instAPats (θ : Subst) : List APat → Option (List Atom)
  | [] => some []
  | ap :: aps =>
    match instAPat θ ap, instAPats θ aps with
    | some a, some rest => some (a :: rest)
    | _, _ => none

/-- A successful pattern instantiation carries the pattern's predicate head. -/
theorem instAPat_head {θ : Subst} {pn : String} {ps : Pats}
    {a : Atom} (h : instAPat θ ⟨⟨pn⟩, ps⟩ = some a) :
    ∃ ts, a = .atom pn ts := by
  simp only [instAPat] at h
  cases hts : instPats θ ps with
  | none => rw [hts] at h; exact nomatch h
  | some ts => rw [hts] at h; exact ⟨ts, (Option.some.inj h).symm⟩

/-- Mapping an injective function preserves duplicate-freedom. The shared home
of the list-bookkeeping helper behind the gadget/witness leaf-table `Nodup`
proofs. -/
theorem nodup_map_of_injective {α β : Type _} {f : α → β}
    (hf : Function.Injective f) {l : List α} (hl : l.Nodup) :
    (l.map f).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact hl.imp fun hne heq => hne (hf heq)

/-! ### Policy rules (spec §4) -/

inductive Mode where
  | strict
  | defeasible
deriving DecidableEq

/-- A critical question: name, answer pattern over the rule's parameters, and
the mandatory/optional flag (spec §4.2). -/
structure Question where
  name      : QuestionId
  answer    : APat
  mandatory : Bool
deriving DecidableEq

/-- A policy rule. `params` are the declared parameters `X1..Xm` (spec §4:
rule well-formedness requires every variable in premises/conclusion/answers
among them); `certifiers` is the per-rule strict-certificate allowlist
(`(beta@version, theory-digest)` pairs); `allowTrusted` gates the `trusted`
assurance. -/
structure Rule where
  mode         : Mode
  params       : List VarId
  premises     : List APat
  concl        : APat
  questions    : List Question
  allowTrusted : Bool
  certifiers   : List (BackendId × Digest)
deriving DecidableEq

def questionNames (r : Rule) : List QuestionId := r.questions.map (·.name)

def mandatoryNames (r : Rule) : List QuestionId :=
  (r.questions.filter (·.mandatory)).map (·.name)

/-! ### Support terms (spec §6) -/

/-- Assurance on an instance. `cert` carries the frozen triple
`(beta, theory-digest, kappa)` — the certificate reference is opaque data;
its acceptance is the `CertOk` premise of the typing relation. -/
inductive Assurance where
  | none
  | trusted
  | cert : BackendId → Digest → CertRef → Assurance
deriving DecidableEq

/-- `w ::= leaf l | r⟨theta ; w* ; {q ↦ w_q} ; {o*} ; assurance⟩`.
The discharge map is an association list `question ↦ discharging term`;
the hole set is the list of open question names. -/
inductive SupportTerm where
  | leaf : LeafId → SupportTerm
  | inst : RuleId → Subst → List SupportTerm →
           List (QuestionId × SupportTerm) → List QuestionId → Assurance →
           SupportTerm

/- Lean 4.32 cannot synthesize equality through the nested recursive
`List SupportTerm` and `List (QuestionId × SupportTerm)` fields.  Decide all
three mutually recursive shapes directly.  This is structural source equality:
in particular the assurance (including an opaque certificate payload) remains
part of the identity. -/
mutual
  def SupportTerm.decEq :
      (a b : SupportTerm) → Decidable (a = b)
    | .leaf x, .leaf y =>
        match _root_.decEq x y with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h =>
            isFalse (by intro hab; injection hab with hxy; exact h hxy)
    | .leaf _, .inst _ _ _ _ _ _ => isFalse (by intro h; cases h)
    | .inst _ _ _ _ _ _, .leaf _ => isFalse (by intro h; cases h)
    | .inst rn θ ws D H α, .inst rn' θ' ws' D' H' α' =>
        match _root_.decEq rn rn' with
        | isFalse h =>
            isFalse (by intro hab; injection hab with hrn; exact h hrn)
        | isTrue hrn =>
          match _root_.decEq θ θ' with
          | isFalse h =>
              isFalse (by intro hab; injection hab with _ hθ; exact h hθ)
          | isTrue hθ =>
            match SupportTerm.decEqList ws ws' with
            | isFalse h =>
                isFalse (by intro hab; injection hab with _ _ hws; exact h hws)
            | isTrue hws =>
              match SupportTerm.decEqDischarges D D' with
              | isFalse h =>
                  isFalse (by
                    intro hab
                    injection hab with _ _ _ hD
                    exact h hD)
              | isTrue hD =>
                match _root_.decEq H H' with
                | isFalse h =>
                    isFalse (by
                      intro hab
                      injection hab with _ _ _ _ hH
                      exact h hH)
                | isTrue hH =>
                  match _root_.decEq α α' with
                  | isFalse h =>
                      isFalse (by
                        intro hab
                        injection hab with _ _ _ _ _ hα
                        exact h hα)
                  | isTrue hα =>
                      isTrue (by
                        cases hrn
                        cases hθ
                        cases hws
                        cases hD
                        cases hH
                        cases hα
                        rfl)

  def SupportTerm.decEqList :
      (xs ys : List SupportTerm) → Decidable (xs = ys)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | x :: xs, y :: ys =>
        match SupportTerm.decEq x y with
        | isFalse h =>
            isFalse (by
              intro hxy
              injection hxy with hhead
              exact h hhead)
        | isTrue h =>
          match SupportTerm.decEqList xs ys with
          | isTrue hs => isTrue (by cases h; cases hs; rfl)
          | isFalse hs =>
              isFalse (by
                intro hxy
                injection hxy with _ htail
                exact hs htail)

  def SupportTerm.decEqDischarges :
      (xs ys : List (QuestionId × SupportTerm)) → Decidable (xs = ys)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | (q, x) :: xs, (q', y) :: ys =>
        match _root_.decEq q q' with
        | isFalse h =>
            isFalse (by
              intro hxy
              injection hxy with hhead
              exact h (congrArg Prod.fst hhead))
        | isTrue hq =>
          match SupportTerm.decEq x y with
          | isFalse h =>
              isFalse (by
                intro hxy
                injection hxy with hhead
                exact h (congrArg Prod.snd hhead))
          | isTrue hx =>
            match SupportTerm.decEqDischarges xs ys with
            | isTrue hs =>
                isTrue (by cases hq; cases hx; cases hs; rfl)
            | isFalse hs =>
                isFalse (by
                  intro hxy
                  injection hxy with _ htail
                  exact hs htail)
end

instance : DecidableEq SupportTerm := SupportTerm.decEq

/- `leaves(w)`: the leaf constants occurring in `w`, discharge subterms
included (spec §6 — the dependency report *is* this set). -/
mutual
  def leaves : SupportTerm → List LeafId
    | .leaf l => [l]
    | .inst _ _ ws D _ _ => leavesList ws ++ leavesDis D
  def leavesList : List SupportTerm → List LeafId
    | [] => []
    | w :: ws => leaves w ++ leavesList ws
  def leavesDis : List (QuestionId × SupportTerm) → List LeafId
    | [] => []
    | (_, w) :: rest => leaves w ++ leavesDis rest
end

/-! ### List helpers (self-contained, `Grounded.lean` style) -/

def memB {α : Type _} [DecidableEq α] (x : α) : List α → Bool
  | [] => false
  | y :: ys => if x = y then true else memB x ys

theorem memB_iff {α : Type _} [DecidableEq α] {x : α} :
    ∀ {l : List α}, memB x l = true ↔ x ∈ l := by
  intro l
  induction l with
  | nil => simp [memB]
  | cons y ys ih =>
    by_cases h : x = y
    · simp [memB, h]
    · simp [memB, h, ih]

/-- Deterministically remove repeated question identifiers. -/
def dedupQuestions : List QuestionId → List QuestionId
  | [] => []
  | q :: qs =>
      let rest := dedupQuestions qs
      if memB q rest then rest else q :: rest

theorem mem_dedupQuestions {q : QuestionId} :
    ∀ qs, q ∈ dedupQuestions qs ↔ q ∈ qs := by
  intro qs
  induction qs with
  | nil => simp [dedupQuestions]
  | cons q' qs ih =>
      by_cases h : q' ∈ dedupQuestions qs
      · have hb : memB q' (dedupQuestions qs) = true := memB_iff.mpr h
        simp only [dedupQuestions, hb, if_true, List.mem_cons]
        constructor
        · intro hq
          exact Or.inr (ih.mp hq)
        · intro hq
          rcases hq with heq | hq
          · subst q'
            exact h
          · exact ih.mpr hq
      · simp [dedupQuestions, memB_iff, h, ih]

theorem dedupQuestions_nodup :
    ∀ qs, (dedupQuestions qs).Nodup := by
  intro qs
  induction qs with
  | nil => simp [dedupQuestions]
  | cons q qs ih =>
      simp only [dedupQuestions]
      split
      · exact ih
      · apply List.nodup_cons.mpr
        rename_i hnot
        exact ⟨fun hmem => hnot (memB_iff.mpr hmem), ih⟩

/-- Collect obligation sets using proved duplicate-eliminating list union. The
traversal order is deterministic, while membership and multiplicity match the
set union in §6.1. -/
def unionAll : List (List QuestionId) → List QuestionId
  | Os => dedupQuestions Os.flatten

theorem unionAll_nodup (Os : List (List QuestionId)) :
    (unionAll Os).Nodup :=
  dedupQuestions_nodup Os.flatten

/-- `H ∩ mandatory(r)`: the obligations an instance's hole set contributes
(§6.1 — optional members of `H` are diagnostics, not obligations). -/
def openMandatory (r : Rule) (H : List QuestionId) : List QuestionId :=
  H.filter (fun n => memB n (mandatoryNames r))

/-- The exact obligation set reported by an instance: child-premise,
child-discharge, and open-mandatory obligations are unioned as sets. -/
def collectObligations (Os DOs : List (List QuestionId)) (r : Rule)
    (H : List QuestionId) : List QuestionId :=
  unionAll (Os ++ DOs ++ [openMandatory r H])

theorem collectObligations_nodup (Os DOs : List (List QuestionId)) (r : Rule)
    (H : List QuestionId) :
    (collectObligations Os DOs r H).Nodup :=
  unionAll_nodup _

theorem append_eq_nil' {α : Type _} {l₁ l₂ : List α} (h : l₁ ++ l₂ = []) :
    l₁ = [] ∧ l₂ = [] := by
  cases l₁ with
  | nil => exact ⟨rfl, h⟩
  | cons x xs => simp at h

theorem getElem?_some_of_lt {α : Type _} :
    ∀ (l : List α) (i : Nat), i < l.length → ∃ a, l[i]? = some a := by
  intro l
  induction l with
  | nil => intro i h; exact absurd h (Nat.not_lt_zero i)
  | cons x xs ih =>
    intro i h
    cases i with
    | zero => exact ⟨x, by simp⟩
    | succ j =>
      obtain ⟨a, ha⟩ := ih j (Nat.lt_of_succ_lt_succ h)
      exact ⟨a, by simpa using ha⟩

theorem lt_of_getElem?_some {α : Type _} :
    ∀ {l : List α} {i : Nat} {a : α}, l[i]? = some a → i < l.length := by
  intro l
  induction l with
  | nil => intro i a h; simp at h
  | cons x xs ih =>
    intro i a h
    cases i with
    | zero => exact Nat.succ_pos _
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      exact Nat.succ_lt_succ (ih h)

theorem getElem?_none_of_ge {α : Type _} :
    ∀ (l : List α) (i : Nat), l.length ≤ i → l[i]? = none := by
  intro l
  induction l with
  | nil => intro i _; simp
  | cons x xs ih =>
    intro i h
    cases i with
    | zero => exact absurd h (by simp)
    | succ j => simpa using ih j (Nat.le_of_succ_le_succ h)

theorem ext_getElem? {α : Type _} :
    ∀ (l₁ l₂ : List α), (∀ i : Nat, l₁[i]? = l₂[i]?) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ h
    cases l₂ with
    | nil => rfl
    | cons y ys => have := h 0; simp at this
  | cons x xs ih =>
    intro l₂ h
    cases l₂ with
    | nil => have := h 0; simp at this
    | cons y ys =>
      have h0 := h 0
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
      have ht : xs = ys := ih ys (fun i => by simpa using h (i + 1))
      rw [h0, ht]

theorem mem_leavesList : ∀ {ws : List SupportTerm} {l : LeafId},
    l ∈ leavesList ws →
      ∃ (i : Nat) (w : SupportTerm), ws[i]? = some w ∧ l ∈ leaves w := by
  intro ws
  induction ws with
  | nil => intro l h; simp [leavesList] at h
  | cons w ws ih =>
    intro l h
    simp only [leavesList] at h
    rcases List.mem_append.mp h with h1 | h2
    · exact ⟨0, w, by simp, h1⟩
    · obtain ⟨i, w', hw', hl⟩ := ih h2
      exact ⟨i + 1, w', by simpa using hw', hl⟩

theorem mem_leavesDis : ∀ {D : List (QuestionId × SupportTerm)} {l : LeafId},
    l ∈ leavesDis D →
      ∃ (j : Nat) (q : QuestionId) (w : SupportTerm),
        D[j]? = some (q, w) ∧ l ∈ leaves w := by
  intro D
  induction D with
  | nil => intro l h; simp [leavesDis] at h
  | cons qw rest ih =>
    intro l h
    obtain ⟨q, w⟩ := qw
    simp only [leavesDis] at h
    rcases List.mem_append.mp h with h1 | h2
    · exact ⟨0, q, w, by simp, h1⟩
    · obtain ⟨j, q', w', hw', hl⟩ := ih h2
      exact ⟨j + 1, q', w', by simpa using hw', hl⟩

theorem mem_mandatoryNames {r : Rule} {qd : Question}
    (hq : qd ∈ r.questions) (hm : qd.mandatory = true) :
    qd.name ∈ mandatoryNames r :=
  List.mem_map.mpr ⟨qd, List.mem_filter.mpr ⟨hq, hm⟩, rfl⟩

theorem mem_questionNames {r : Rule} {qd : Question} (hq : qd ∈ r.questions) :
    qd.name ∈ questionNames r :=
  List.mem_map.mpr ⟨qd, hq, rfl⟩

/-! ### The typing judgment (spec §6.1, v0.1-frozen) -/

/-- Backend acceptance, indexed by the frozen `cert` triple: `CertOk β h κ As C`
abstracts "registered backend `β` with allowlisted theory digest `h` accepts
certificate `κ` for the encoded step" — it consumes the *instantiated premise
patterns* `As` (spec §5: `Delta = [encode_beta(P_i theta)]`), not the premise
terms' conclusions. `certOkOf` below instantiates it from a registry. -/
inductive AssuranceOk (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop)
    (r : Rule) (As : List Atom) (C : Atom) : Assurance → Prop where
  | defeasible (h : r.mode = .defeasible) : AssuranceOk CertOk r As C .none
  | trusted (h : r.mode = .strict) (ht : r.allowTrusted = true) :
      AssuranceOk CertOk r As C .trusted
  | cert {β : BackendId} {hd : Digest} {κ : CertRef}
      (h : r.mode = .strict)
      (hallow : (β, hd) ∈ r.certifiers)
      (hacc : CertOk β hd κ As C) :
      AssuranceOk CertOk r As C (.cert β hd κ)

/-- The non-recursive premises of the §6.1 instance rule, bundled. `As` are
the instantiated premise patterns, `Cs`/`Os` the premise terms' conclusions
and obligations, `DCs`/`DOs` the same for discharge terms. -/
structure InstSide (canon : String → String) (Pi : RuleId → Option Rule)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop)
    (rn : RuleId) (θ : Subst) (r : Rule)
    (ws : List SupportTerm) (D : List (QuestionId × SupportTerm))
    (H : List QuestionId) (α : Assurance) (As Cs : List Atom)
    (Os : List (List QuestionId))
    (DCs : List Atom) (DOs : List (List QuestionId)) (C : Atom) : Prop where
  /-- the rule is policy content, looked up — never program-defined (§4) -/
  rule   : Pi rn = some r
  /-- `theta` is duplicate-free … -/
  θNodup : (θ.map Prod.fst).Nodup
  /-- … and `dom(theta) = {X1..Xm}` exactly — the §6.1 side condition (no
  extra bindings, no omitted declared parameters, questions/exceptions
  included since their variables are among `params` by rule wf, §4.1) -/
  θDom   : ∀ x : VarId, x ∈ θ.map Prod.fst ↔ x ∈ r.params
  /-- premise patterns instantiate … -/
  prems  : instAPats θ r.premises = some As
  /-- … and so does the conclusion pattern: `concl(w) = Ap_c theta` -/
  concl  : instAPat θ r.concl = some C
  lenAs  : ws.length = As.length
  lenCs  : Cs.length = ws.length
  lenOs  : Os.length = ws.length
  /-- premise identity is `≡` (folded into `supports(...)`, §6.1) -/
  premEq : ∀ (i : Nat) (A B : Atom),
             Cs[i]? = some A → As[i]? = some B → equiv canon A B
  lenDCs : DCs.length = D.length
  lenDOs : DOs.length = D.length
  /-- each discharge answers its question's pattern under the same `theta` (§4.2) -/
  ans    : ∀ (j : Nat) (q : QuestionId) (w : SupportTerm) (A : Atom),
             D[j]? = some (q, w) → DCs[j]? = some A →
             ∃ qd, qd ∈ r.questions ∧ qd.name = q ∧
               ∃ Aq, instAPat θ qd.answer = some Aq ∧ equiv canon A Aq
  /-- the policy's question names are duplicate-free (rule wf) … -/
  qNodup : (questionNames r).Nodup
  /-- … as are the discharge keys … -/
  dNodup : (D.map Prod.fst).Nodup
  /-- … and the hole set — so `D ⊎ H = questions(r)` is a genuine partition -/
  hNodup : H.Nodup
  /-- `D ⊎ H = questions(r)`: cover … -/
  cover  : ∀ qd, qd ∈ r.questions → qd.name ∈ D.map Prod.fst ∨ qd.name ∈ H
  /-- … disjointness … -/
  disj   : ∀ n, n ∈ D.map Prod.fst → n ∉ H
  /-- … and no junk on either side (a question absent from both is ill-formed) -/
  keysD  : ∀ n, n ∈ D.map Prod.fst → n ∈ questionNames r
  keysH  : ∀ n, n ∈ H → n ∈ questionNames r
  /-- strict rules declare no questions (§5), so `D` and `H` are empty -/
  strictNoQ : r.mode = .strict → D = [] ∧ H = []
  /-- the `assurance(m, alpha)` side condition -/
  assur  : AssuranceOk CertOk r As C α

/-- `Sigma; Pi; Gamma; R |- w : supports(p) ▷ O`, §6.1's two rules. The
conclusion index is the *exact* `concl(w)`; `≡`-closure is applied where the
spec applies it (premises, discharges, and the claim-level `Supports`).
Recursive premises are `l[i]?`-indexed so each occurrence sits directly under
`∀`/`→`. -/
inductive HasSupport (canon : String → String) (Pi : RuleId → Option Rule)
    (Gamma : LeafId → Option Atom)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop) :
    SupportTerm → Atom → List QuestionId → Prop where
  | leaf {l : LeafId} {p : Atom} (hΓ : Gamma l = some p) :
      HasSupport canon Pi Gamma CertOk (.leaf l) p []
  | inst {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
      {D : List (QuestionId × SupportTerm)} {H : List QuestionId}
      {α : Assurance} {r : Rule} {As Cs : List Atom}
      {Os : List (List QuestionId)}
      {DCs : List Atom} {DOs : List (List QuestionId)} {C : Atom}
      (hside : InstSide canon Pi CertOk rn θ r ws D H α As Cs Os DCs DOs C)
      (hprems : ∀ (i : Nat) (w : SupportTerm) (A : Atom) (O : List QuestionId),
        ws[i]? = some w → Cs[i]? = some A → Os[i]? = some O →
        HasSupport canon Pi Gamma CertOk w A O)
      (hdis : ∀ (j : Nat) (q : QuestionId) (w : SupportTerm) (A : Atom)
        (O : List QuestionId), D[j]? = some (q, w) → DCs[j]? = some A →
        DOs[j]? = some O → HasSupport canon Pi Gamma CertOk w A O) :
      HasSupport canon Pi Gamma CertOk (.inst rn θ ws D H α) C
        (collectObligations Os DOs r H)

/-- `w supports p` at claim level (spec §3.1/§6.1): the unique conclusion is
`≡`-identical to `p`. Result 11's decidability lands with the executable
checker; this is the relational layer. -/
def Supports (canon : String → String) (Pi : RuleId → Option Rule)
    (Gamma : LeafId → Option Atom)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop)
    (w : SupportTerm) (p : Atom) : Prop :=
  ∃ C O, HasSupport canon Pi Gamma CertOk w C O ∧ equiv canon C p

/-! ### Result 3 (leaf half): dependency accountability -/

/-- **Every leaf used by a typed term is declared.** The reported dependency
set is `leaves w` by definition (§6), so with this lemma the report is exactly
the declared leaves the term touches — the accountability inversion. -/
theorem leaves_declared {canon Pi Gamma CertOk} {w : SupportTerm} {C : Atom}
    {O : List QuestionId} (h : HasSupport canon Pi Gamma CertOk w C O) :
    ∀ l, l ∈ leaves w → ∃ p, Gamma l = some p := by
  induction h with
  | leaf hΓ =>
    intro l hl
    simp only [leaves, List.mem_singleton] at hl
    subst hl
    exact ⟨_, hΓ⟩
  | @inst rn θ ws D H α r As Cs Os DCs DOs C hside hprems hdis ihprems ihdis =>
    intro l hl
    simp only [leaves] at hl
    rcases List.mem_append.mp hl with hws | hD
    · obtain ⟨i, w', hw', hl'⟩ := mem_leavesList hws
      have hi := lt_of_getElem?_some hw'
      obtain ⟨A, hA⟩ := getElem?_some_of_lt Cs i
        (by have := hside.lenCs; omega)
      obtain ⟨O', hO⟩ := getElem?_some_of_lt Os i
        (by have := hside.lenOs; omega)
      exact ihprems i w' A O' hw' hA hO l hl'
    · obtain ⟨j, q, w', hw', hl'⟩ := mem_leavesDis hD
      have hj := lt_of_getElem?_some hw'
      obtain ⟨A, hA⟩ := getElem?_some_of_lt DCs j
        (by have := hside.lenDCs; omega)
      obtain ⟨O', hO⟩ := getElem?_some_of_lt DOs j
        (by have := hside.lenDOs; omega)
      exact ihdis j q w' A O' hw' hA hO l hl'

/-! ### Result 1 (uniqueness half): support checking is deterministic -/

/-- **Uniqueness.** A term has one conclusion and one obligation set: checking
is a partial function of the term. `Lara.Check.Support` provides the executable
inference function and `Lara.Check.SupportProof` proves its exact adequacy. -/
theorem hasSupport_unique {canon Pi Gamma CertOk} {w : SupportTerm}
    {C₁ : Atom} {O₁ : List QuestionId}
    (h₁ : HasSupport canon Pi Gamma CertOk w C₁ O₁) :
    ∀ {C₂ O₂}, HasSupport canon Pi Gamma CertOk w C₂ O₂ → C₁ = C₂ ∧ O₁ = O₂ := by
  induction h₁ with
  | leaf hΓ =>
    intro C₂ O₂ h₂
    cases h₂ with
    | leaf hΓ' => exact ⟨Option.some.inj (hΓ.symm.trans hΓ'), rfl⟩
  | @inst rn θ ws D H α r As Cs Os DCs DOs C hside hprems hdis ihprems ihdis =>
    intro C₂ O₂ h₂
    cases h₂ with
    | @inst _ _ _ _ _ _ r' As' Cs' Os' DCs' DOs' _ hside' hprems' hdis' =>
      have hr : r' = r := Option.some.inj (hside'.rule.symm.trans hside.rule)
      subst hr
      have hAs : As' = As := Option.some.inj (hside'.prems.symm.trans hside.prems)
      subst hAs
      have hC : C = C₂ := Option.some.inj (hside.concl.symm.trans hside'.concl)
      have hOs : Os = Os' := by
        apply ext_getElem?
        intro i
        by_cases hi : i < ws.length
        · obtain ⟨w', hw⟩ := getElem?_some_of_lt ws i hi
          obtain ⟨A, hA⟩ := getElem?_some_of_lt Cs i
            (by have := hside.lenCs; omega)
          obtain ⟨O', hO⟩ := getElem?_some_of_lt Os i
            (by have := hside.lenOs; omega)
          obtain ⟨A', hA'⟩ := getElem?_some_of_lt Cs' i
            (by have := hside'.lenCs; omega)
          obtain ⟨O'', hO'⟩ := getElem?_some_of_lt Os' i
            (by have := hside'.lenOs; omega)
          have huniq := ihprems i w' A O' hw hA hO (hprems' i w' A' O'' hw hA' hO')
          rw [hO, hO', huniq.2]
        · rw [getElem?_none_of_ge Os i (by have := hside.lenOs; omega),
              getElem?_none_of_ge Os' i (by have := hside'.lenOs; omega)]
      have hDOs : DOs = DOs' := by
        apply ext_getElem?
        intro j
        by_cases hj : j < D.length
        · obtain ⟨qw, hqw⟩ := getElem?_some_of_lt D j hj
          obtain ⟨q, w'⟩ := qw
          obtain ⟨A, hA⟩ := getElem?_some_of_lt DCs j
            (by have := hside.lenDCs; omega)
          obtain ⟨O', hO⟩ := getElem?_some_of_lt DOs j
            (by have := hside.lenDOs; omega)
          obtain ⟨A', hA'⟩ := getElem?_some_of_lt DCs' j
            (by have := hside'.lenDCs; omega)
          obtain ⟨O'', hO'⟩ := getElem?_some_of_lt DOs' j
            (by have := hside'.lenDOs; omega)
          have huniq := ihdis j q w' A O' hqw hA hO (hdis' j q w' A' O'' hqw hA' hO')
          rw [hO, hO', huniq.2]
        · rw [getElem?_none_of_ge DOs j (by have := hside.lenDOs; omega),
              getElem?_none_of_ge DOs' j (by have := hside'.lenDOs; omega)]
      exact ⟨hC, by simp only [collectObligations]; rw [hOs, hDOs]⟩

/-! ### Generic facts about the judgment

These are the inversion and weakening lemmas every downstream module needs
about `HasSupport` itself — none is specific to a checker, an update, or a
link. They live here, at the judgment's module, so that no downstream module
re-proves them privately. -/

/-- **Root inversion.** A derivation of an instance is headed by its rule: the
rule resolves, and the derived conclusion is the rule's instantiated
conclusion. -/
theorem hasSupport_inst_root {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId}
    {α : Assurance} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk (.inst rn θ ws D H α) C O) :
    ∃ r, Pi rn = some r ∧ instAPat θ r.concl = some C := by
  cases h with
  | inst hside _ _ => exact ⟨_, hside.rule, hside.concl⟩

/-- **Leaf inversion.** A derivation of a leaf is the environment's entry for
it. -/
theorem hasSupport_leaf_gamma {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {l : LeafId} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk (.leaf l) C O) :
    Gamma l = some C := by
  cases h with
  | leaf hΓ => exact hΓ

/-- **Γ-weakening.** A support derivation survives any extension of the leaf
environment: the judgment only ever *reads* Γ at the leaves it mentions. -/
theorem hasSupport_mono_gamma {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma Gamma' : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (hext : ∀ l p, Gamma l = some p → Gamma' l = some p)
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk w C O) :
    HasSupport canon Pi Gamma' CertOk w C O := by
  induction h with
  | leaf hGamma => exact .leaf (hext _ _ hGamma)
  | inst hside hprems hdis ihprems ihdis => exact .inst hside ihprems ihdis

/-- `Supports` respects `≡`: one term cannot support two `≢` claims. With
uniqueness this is result 11's functionality at claim level. -/
theorem supports_resp_equiv {canon Pi Gamma CertOk} {w : SupportTerm}
    {p p' : Atom} (h₁ : Supports canon Pi Gamma CertOk w p)
    (h₂ : Supports canon Pi Gamma CertOk w p') :
    equiv canon p p' := by
  obtain ⟨C, O, hC, he⟩ := h₁
  obtain ⟨C', O', hC', he'⟩ := h₂
  have hcc : C = C' := (hasSupport_unique hC hC').1
  exact equiv_trans canon (equiv_symm canon he) (hcc ▸ he')

/-! ### The §6.1 accounting invariants as inversion lemmas -/

/-- A strict instance has an empty discharge map and hole set (spec §5/§6.1's
`m = strict ⟹ D = {} ∧ H = {}`). -/
theorem strict_no_questions {canon Pi Gamma CertOk}
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {α : Assurance}
    {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk (.inst rn θ ws D H α) C O)
    {r : Rule} (hr : Pi rn = some r) (hm : r.mode = .strict) :
    D = [] ∧ H = [] := by
  cases h with
  | @inst _ _ _ _ _ _ r' As Cs Os DCs DOs C hside _ _ =>
    have : r' = r := Option.some.inj (hside.rule.symm.trans hr)
    subst this
    exact hside.strictNoQ hm

/-- **Complete instances discharge every mandatory question.** `O = []` at an
instance root forces `H ∩ mandatory(r) = []`, and the `D (+) H` cover then
puts each mandatory question's name in the discharge map — the §6.1
accounting invariant doing its job. -/
theorem complete_mandatory_discharged {canon Pi Gamma CertOk}
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {α : Assurance}
    {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk (.inst rn θ ws D H α) C O)
    (hO : O = []) {r : Rule} (hr : Pi rn = some r) :
    ∀ qd ∈ r.questions, qd.mandatory = true → qd.name ∈ D.map Prod.fst := by
  cases h with
  | @inst _ _ _ _ _ _ r' As Cs Os DCs DOs C' hside _ _ =>
    intro qd hq hm
    have hrr : r' = r := Option.some.inj (hside.rule.symm.trans hr)
    rw [hrr] at hside hO
    have hOM : openMandatory r H = [] := by
      cases hom : openMandatory r H with
      | nil => rfl
      | cons q qs =>
          have hmem : q ∈ collectObligations Os DOs r H := by
            rw [collectObligations, unionAll]
            apply (mem_dedupQuestions _).mpr
            simp [hom]
          rw [hO] at hmem
          simp at hmem
    rcases hside.cover qd hq with hk | hh
    · exact hk
    · have hmem : qd.name ∈ openMandatory r H :=
        List.mem_filter.mpr ⟨hh, memB_iff.mpr (mem_mandatoryNames hq hm)⟩
      rw [hOM] at hmem
      cases hmem

/-- **The `D ⊎ H` partition, extensionally.** With the `Nodup` invariants of
`InstSide`, cover + disjointness + no-junk make discharge keys and holes a
genuine partition of the rule's question names: membership on either side is
equivalent to being a declared question, and the two sides never overlap. -/
theorem dh_partition {canon Pi CertOk}
    {rn : RuleId} {θ : Subst} {r : Rule} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {α : Assurance}
    {As Cs : List Atom} {Os : List (List QuestionId)}
    {DCs : List Atom} {DOs : List (List QuestionId)} {C : Atom}
    (hside : InstSide canon Pi CertOk rn θ r ws D H α As Cs Os DCs DOs C) :
    (∀ n, n ∈ questionNames r ↔ (n ∈ D.map Prod.fst ∨ n ∈ H)) ∧
      ∀ n, n ∈ D.map Prod.fst → n ∉ H := by
  refine ⟨fun n => ⟨fun hn => ?_, fun hn => ?_⟩, hside.disj⟩
  · obtain ⟨qd, hqd, hname⟩ := List.mem_map.mp hn
    exact hname ▸ hside.cover qd hqd
  · rcases hn with h | h
    · exact hside.keysD n h
    · exact hside.keysH n h

/-! ### The seam: §6.1's `cert` assurance meets Theorem 1 -/

/-- One registered outer backend identity: one fixed backend *core* per exact
`(name, version)`, plus an inner resolver that returns only the digest's
theory **data**.  Digest resolution cannot introduce behavior — every digest
of a registered identity is replayed by the same core, and the selected
theory enters acceptance only as data appended to the consulted context,
where the core's coverage law ranges over it
(`certOkBOf_theory_covers`). -/
structure RegisteredBackend (canon : String → String) where
  /-- The fixed backend core for this `(name, version)` identity. -/
  core : Strict.Backend canon
  /-- Resolve a selected digest to that digest's theory data, core-encoded. -/
  resolveTheory : Digest → Option (List core.Form)

/-- Backend-first closed registry.  The complete `(name, version)` is the outer
identity; digest selection occurs only after that exact lookup succeeds. -/
abbrev BackendRegistry (canon : String → String) :=
  BackendId → Option (RegisteredBackend canon)

/-- `CertOk` from a backend-first registry: exact identity `β` resolves to the
fixed core before digest `h` resolves to theory data, and the core receives
the unchanged symbolic certificate, the encoded source premises, and that
data-only theory. -/
def certOkOf {canon : String → String} (reg : BackendRegistry canon) :
    BackendId → Digest → CertRef → List Atom → Atom → Prop :=
  fun β h κ As C =>
    match reg β with
    | none => False
    | some registered =>
        match registered.resolveTheory h with
        | none => False
        | some T =>
            registered.core.accepts T κ (As.map registered.core.enc)
              (registered.core.enc C)

/-- Executable certificate check over the same backend-first resolution path. -/
def certOkBOf {canon : String → String} (reg : BackendRegistry canon)
    (β : BackendId) (h : Digest) (κ : CertRef) (As : List Atom)
    (C : Atom) : Bool :=
  -- β -> closed registry -> fixed core; h -> theory data -> exact replay
  match reg β with
  | none => false
  | some registered =>
      match registered.resolveTheory h with
      | none => false
      | some T =>
          registered.core.replay T κ (As.map registered.core.enc)
            (registered.core.enc C)

/-- Executable replay is adequate for proposition-level certificate
acceptance, including both lookup layers. -/
theorem certOkBOf_iff {canon : String → String} (reg : BackendRegistry canon)
    (β : BackendId) (h : Digest) (κ : CertRef) (As : List Atom)
    (C : Atom) :
    certOkBOf reg β h κ As C = true ↔ certOkOf reg β h κ As C := by
  cases hreg : reg β with
  | none => simp [certOkBOf, certOkOf, hreg]
  | some registered =>
      cases hresolve : registered.resolveTheory h with
      | none => simp [certOkBOf, certOkOf, hreg, hresolve]
      | some T =>
          simpa [certOkBOf, certOkOf, hreg, hresolve] using
            (registered.core.replay_iff T κ (As.map registered.core.enc)
              (registered.core.enc C))

/-- **Registry-level theory coverage.** Under one registered identity, a
digest swap is observable only through reported theory slots: two digests
whose resolved theory data agree on every reported theory slot replay
identically.  Because the core is fixed per `(name, version)` and a digest
resolves only to data, hidden theory consultation through the digest
mechanism is impossible — this was false for a registry whose digest
resolver could return arbitrary backend behavior. -/
theorem certOkBOf_theory_covers {canon : String → String}
    {reg : BackendRegistry canon} {β : BackendId} {h h' : Digest}
    {κ : CertRef} {As : List Atom} {C : Atom}
    {registered : RegisteredBackend canon}
    {T T' : List registered.core.Form}
    (hreg : reg β = some registered)
    (hT : registered.resolveTheory h = some T)
    (hT' : registered.resolveTheory h' = some T')
    (hag : ∀ i, i ∈ registered.core.uses κ → As.length ≤ i →
      T[i - As.length]? = T'[i - As.length]?) :
    certOkBOf reg β h κ As C = certOkBOf reg β h' κ As C := by
  simp only [certOkBOf, hreg, hT, hT']
  exact registered.core.replay_theory_covers κ _ _
    (by simpa [List.length_map] using hag)

/-- The §6.1 `cert` side condition composed with the abstract seam is exactly
Theorem 1: an accepted strict instance's conclusion is a backend consequence
of its instantiated premises, for the registered backend the assurance names.
§6 typing and §5 soundness agree. -/
theorem certOkOf_strict_step {canon : String → String}
    {reg : BackendRegistry canon}
    {β : BackendId} {h : Digest} {κ : CertRef} {As : List Atom} {C : Atom}
    (hacc : certOkOf reg β h κ As C) :
    ∃ registered T, reg β = some registered ∧
      registered.resolveTheory h = some T ∧
      registered.core.models T (As.map registered.core.enc)
        (registered.core.enc C) := by
  simp only [certOkOf] at hacc
  split at hacc
  · contradiction
  · rename_i registered hregistered
    split at hacc
    · contradiction
    · rename_i T hT
      exact ⟨registered, T, hregistered, hT,
        registered.core.sound _ _ _ _ hacc⟩

/-! ### Result 3 (certificate half): strict-dependency accountability

`certDeps(w)` (spec §6) is the union, over every certificate-assured instance
in the term, of that certificate's reported dependencies, each resolved to a
`CertDep`: a premise slot resolved to its instantiated premise atom, or an
entry of the certificate's digest-addressed theory `(β, h)` — the same
premise/theory split as the Haskell `Lara.Strict.Dependency`.  No slot is
filtered: every reported index resolves to exactly one constructor.  The
theorems mirror `leaves_declared`: `certDeps` collects exactly the per-node
reports (`mem_certDeps_step` / `certStep_deps_subset`); every premise entry
resolves to the corresponding premise subterm of its own reporting node
(`certDeps_resolved`); every theory entry names a genuine entry of the
digest-resolved theory data (`certDeps_theory_valid`); and every accepted
certificate's conclusion follows from just the reported entries of the full
consulted context (`cert_steps_accounted`). -/

/-- A resolved strict-certificate dependency (spec §6; the Haskell
`Lara.Strict.Dependency` premise/theory split): premise slot `i`, resolved to
its instantiated premise atom, or entry `t` of the reporting certificate's
digest-addressed theory `(β, h)`. -/
inductive CertDep where
  | premise : Nat → Atom → CertDep
  | theoryEntry : BackendId → Digest → Nat → CertDep
deriving DecidableEq

/-- Resolve one reported slot against the instantiated premises: a slot below
`As.length` names that premise occurrence; any other slot names entry
`i - As.length` of the certificate's digest-addressed theory.  Total — no
reported slot is dropped. -/
def resolveSlot (β : BackendId) (h : Digest) (As : List Atom) (i : Nat) :
    CertDep :=
  match As[i]? with
  | some A => .premise i A
  | none => .theoryEntry β h (i - As.length)

/-- The reported dependencies of one support-term node: for a
certificate-assured instance whose rule, premise instantiation, and backend
resolve, every reported slot resolved via `resolveSlot`; empty for any other
node.  A typed certificate node always resolves (`cert_node_accounted`). -/
def stepDeps {canon : String → String} (Pi : RuleId → Option Rule)
    (reg : BackendRegistry canon) : SupportTerm → List CertDep
  | .inst rn θ _ _ _ (.cert β h κ) =>
    (match Pi rn with
     | none => []
     | some r =>
       match instAPats θ r.premises with
       | none => []
       | some As =>
         match reg β with
         | none => []
         | some registered =>
           match registered.resolveTheory h with
           | none => []
           | some _ => (registered.core.uses κ).map (resolveSlot β h As))
  | _ => []

/-- `CertStepIn w u`: the certificate-assured instance node `u` occurs in `w`
— at the root, inside a premise subterm, or inside a discharge subterm.  The
occurrence carries the node itself, so downstream theorems can name that
node's own premise subterms. -/
inductive CertStepIn : SupportTerm → SupportTerm → Prop where
  | here {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
      {D : List (QuestionId × SupportTerm)} {H : List QuestionId}
      {β : BackendId} {hd : Digest} {κ : CertRef} :
      CertStepIn (.inst rn θ ws D H (.cert β hd κ))
        (.inst rn θ ws D H (.cert β hd κ))
  | prem {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
      {D : List (QuestionId × SupportTerm)} {H : List QuestionId}
      {α : Assurance} {u : SupportTerm} {i : Nat} {w : SupportTerm}
      (hw : ws[i]? = some w) (hstep : CertStepIn w u) :
      CertStepIn (.inst rn θ ws D H α) u
  | dis {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
      {D : List (QuestionId × SupportTerm)} {H : List QuestionId}
      {α : Assurance} {u : SupportTerm} {j : Nat} {q : QuestionId}
      {w : SupportTerm}
      (hw : D[j]? = some (q, w)) (hstep : CertStepIn w u) :
      CertStepIn (.inst rn θ ws D H α) u

/- `certDeps(w)` (spec §6): the strict-certificate half of the dependency
report `leaves(w) ∪ certDeps(w)` — every certificate node's resolved report,
discharge subterms included. -/
mutual
  def certDeps {canon : String → String} (Pi : RuleId → Option Rule)
      (reg : BackendRegistry canon) : SupportTerm → List CertDep
    | .leaf _ => []
    | .inst rn θ ws D H α =>
        stepDeps Pi reg (.inst rn θ ws D H α) ++
          certDepsList Pi reg ws ++ certDepsDis Pi reg D
  def certDepsList {canon : String → String} (Pi : RuleId → Option Rule)
      (reg : BackendRegistry canon) : List SupportTerm → List CertDep
    | [] => []
    | w :: ws => certDeps Pi reg w ++ certDepsList Pi reg ws
  def certDepsDis {canon : String → String} (Pi : RuleId → Option Rule)
      (reg : BackendRegistry canon) :
      List (QuestionId × SupportTerm) → List CertDep
    | [] => []
    | (_, w) :: rest => certDeps Pi reg w ++ certDepsDis Pi reg rest
end

theorem mem_certDepsList {canon : String → String} {Pi : RuleId → Option Rule}
    {reg : BackendRegistry canon} :
    ∀ {ws : List SupportTerm} {d : CertDep}, d ∈ certDepsList Pi reg ws →
      ∃ (i : Nat) (w : SupportTerm), ws[i]? = some w ∧ d ∈ certDeps Pi reg w := by
  intro ws
  induction ws with
  | nil => intro d h; simp [certDepsList] at h
  | cons w ws ih =>
    intro d h
    simp only [certDepsList] at h
    rcases List.mem_append.mp h with h1 | h2
    · exact ⟨0, w, by simp, h1⟩
    · obtain ⟨i, w', hw', hd'⟩ := ih h2
      exact ⟨i + 1, w', by simpa using hw', hd'⟩

theorem mem_certDepsDis {canon : String → String} {Pi : RuleId → Option Rule}
    {reg : BackendRegistry canon} :
    ∀ {D : List (QuestionId × SupportTerm)} {d : CertDep},
      d ∈ certDepsDis Pi reg D →
      ∃ (j : Nat) (q : QuestionId) (w : SupportTerm),
        D[j]? = some (q, w) ∧ d ∈ certDeps Pi reg w := by
  intro D
  induction D with
  | nil => intro d h; simp [certDepsDis] at h
  | cons qw rest ih =>
    intro d h
    obtain ⟨q, w⟩ := qw
    simp only [certDepsDis] at h
    rcases List.mem_append.mp h with h1 | h2
    · exact ⟨0, q, w, by simp, h1⟩
    · obtain ⟨j, q', w', hw', hd'⟩ := ih h2
      exact ⟨j + 1, q', w', by simpa using hw', hd'⟩

theorem certDeps_mem_list {canon : String → String} {Pi : RuleId → Option Rule}
    {reg : BackendRegistry canon} :
    ∀ {ws : List SupportTerm} {i : Nat} {w : SupportTerm} {d : CertDep},
      ws[i]? = some w → d ∈ certDeps Pi reg w → d ∈ certDepsList Pi reg ws := by
  intro ws
  induction ws with
  | nil => intro i w d hw _; simp at hw
  | cons w₀ ws ih =>
    intro i w d hw hd'
    cases i with
    | zero =>
      have : w₀ = w := by simpa using hw
      subst this
      exact List.mem_append.mpr (Or.inl hd')
    | succ k =>
      exact List.mem_append.mpr (Or.inr (ih (by simpa using hw) hd'))

theorem certDeps_mem_dis {canon : String → String} {Pi : RuleId → Option Rule}
    {reg : BackendRegistry canon} :
    ∀ {D : List (QuestionId × SupportTerm)} {j : Nat} {q : QuestionId}
      {w : SupportTerm} {d : CertDep},
      D[j]? = some (q, w) → d ∈ certDeps Pi reg w → d ∈ certDepsDis Pi reg D := by
  intro D
  induction D with
  | nil => intro j q w d hw _; simp at hw
  | cons qw rest ih =>
    intro j q w d hw hd'
    obtain ⟨q₀, w₀⟩ := qw
    cases j with
    | zero =>
      have h0 : q₀ = q ∧ w₀ = w := by simpa using hw
      obtain ⟨_, rfl⟩ := h0
      exact List.mem_append.mpr (Or.inl hd')
    | succ k =>
      exact List.mem_append.mpr (Or.inr (ih (by simpa using hw) hd'))

/-- A certificate node occurring in a typed term is itself typed, under the
same contexts. -/
theorem certStepIn_typed {canon Pi Gamma CertOk} {w : SupportTerm} {C : Atom}
    {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk w C O) :
    ∀ u, CertStepIn w u →
      ∃ C' O', HasSupport canon Pi Gamma CertOk u C' O' := by
  induction h with
  | leaf hΓ =>
    intro u hstep
    cases hstep
  | @inst rn θ ws D H α r As Cs Os DCs DOs C hside hprems hdis ihprems ihdis =>
    intro u hstep
    cases hstep with
    | here => exact ⟨_, _, .inst hside hprems hdis⟩
    | @prem _ _ _ _ _ _ _ i w' hw hstep' =>
      have hi := lt_of_getElem?_some hw
      obtain ⟨A, hA⟩ := getElem?_some_of_lt Cs i
        (by have := hside.lenCs; omega)
      obtain ⟨O', hO⟩ := getElem?_some_of_lt Os i
        (by have := hside.lenOs; omega)
      exact ihprems i w' A O' hw hA hO u hstep'
    | @dis _ _ _ _ _ _ _ j q w' hw hstep' =>
      have hj := lt_of_getElem?_some hw
      obtain ⟨A, hA⟩ := getElem?_some_of_lt DCs j
        (by have := hside.lenDCs; omega)
      obtain ⟨O', hO⟩ := getElem?_some_of_lt DOs j
        (by have := hside.lenDOs; omega)
      exact ihdis j q w' A O' hw hA hO u hstep'

/-- `certOkOf` composed with the backend's semantic accounting law: an
accepted certificate's encoded conclusion is a consequence of just the
reported entries of the full consulted context — selected premise encodings
and selected digest-addressed theory entries alike; `certOkOf_strict_step`
strengthened from the full context to the reported slots. -/
theorem certOkOf_uses_account {canon : String → String}
    {reg : BackendRegistry canon}
    {β : BackendId} {h : Digest} {κ : CertRef} {As : List Atom} {C : Atom}
    (hacc : certOkOf reg β h κ As C) :
    ∃ registered T, reg β = some registered ∧
      registered.resolveTheory h = some T ∧
      registered.core.modelsFull
        (Strict.selectSlots (As.map registered.core.enc ++ T)
          (registered.core.uses κ))
        (registered.core.enc C) := by
  simp only [certOkOf] at hacc
  split at hacc
  · contradiction
  · rename_i registered hregistered
    split at hacc
    · contradiction
    · rename_i T hT
      exact ⟨registered, T, hregistered, hT,
        registered.core.uses_account _ _ _ hacc⟩

/-- **Result 3 (certificate half), per-node accounting.** A typed
certificate-assured node resolves end to end — strict rule, allowlisted
`(β, h)`, instantiated premises and conclusion, registered core, resolved
theory data — its report is exactly the core's `uses` resolved slotwise, and
its encoded conclusion is a consequence of just the reported entries of the
full consulted context: selected premises and selected digest-addressed
theory entries alike. -/
theorem cert_node_accounted {canon Pi Gamma} {reg : BackendRegistry canon}
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId}
    {β : BackendId} {hd : Digest} {κ : CertRef} {C : Atom}
    {O : List QuestionId}
    (h : HasSupport canon Pi Gamma (certOkOf reg)
      (.inst rn θ ws D H (.cert β hd κ)) C O) :
    ∃ r As registered T,
      Pi rn = some r ∧ r.mode = .strict ∧ (β, hd) ∈ r.certifiers ∧
      instAPats θ r.premises = some As ∧ instAPat θ r.concl = some C ∧
      reg β = some registered ∧ registered.resolveTheory hd = some T ∧
      stepDeps Pi reg (.inst rn θ ws D H (.cert β hd κ)) =
        (registered.core.uses κ).map (resolveSlot β hd As) ∧
      registered.core.modelsFull
        (Strict.selectSlots (As.map registered.core.enc ++ T)
          (registered.core.uses κ))
        (registered.core.enc C) := by
  cases h with
  | @inst _ _ _ _ _ _ r As Cs Os DCs DOs _ hside hprems hdis =>
    cases hside.assur with
    | cert hm hallow hacc =>
      obtain ⟨registered, T, hreg, hres, hmodels⟩ := certOkOf_uses_account hacc
      refine ⟨r, As, registered, T, hside.rule, hm, hallow, hside.prems,
        hside.concl, hreg, hres, ?_, hmodels⟩
      simp [stepDeps, hside.rule, hside.prems, hreg, hres]

/-- **Per-step accounting over the whole term.** Every certificate-assured
node occurring anywhere in a typed term is dependency-accounted: no free
strict assumption is hidden anywhere in the term. -/
theorem cert_steps_accounted {canon Pi Gamma} {reg : BackendRegistry canon}
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma (certOkOf reg) w C O) :
    ∀ rn θ ws D H β hd κ,
      CertStepIn w (.inst rn θ ws D H (.cert β hd κ)) →
      ∃ r As Cn registered T,
        Pi rn = some r ∧ r.mode = .strict ∧ (β, hd) ∈ r.certifiers ∧
        instAPats θ r.premises = some As ∧ instAPat θ r.concl = some Cn ∧
        reg β = some registered ∧ registered.resolveTheory hd = some T ∧
        registered.core.modelsFull
          (Strict.selectSlots (As.map registered.core.enc ++ T)
            (registered.core.uses κ))
          (registered.core.enc Cn) := by
  intro rn θ ws D H β hd κ hstep
  obtain ⟨C', O', h'⟩ := certStepIn_typed h _ hstep
  obtain ⟨r, As, registered, T, hr, hm, hallow, hAs, hC, hreg, hres, _,
    hmodels⟩ := cert_node_accounted h'
  exact ⟨r, As, C', registered, T, hr, hm, hallow, hAs, hC, hreg, hres,
    hmodels⟩

/-- Collection, one direction: every entry of `certDeps w` is a reported
dependency of some certificate node occurring in `w`. -/
theorem mem_certDeps_step {canon Pi Gamma} {reg : BackendRegistry canon}
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma (certOkOf reg) w C O) :
    ∀ d, d ∈ certDeps Pi reg w →
      ∃ u, CertStepIn w u ∧ d ∈ stepDeps Pi reg u := by
  induction h with
  | leaf hΓ => intro d hd'; simp [certDeps] at hd'
  | @inst rn θ ws D H α r As Cs Os DCs DOs C hside hprems hdis ihprems ihdis =>
    intro d hd'
    simp only [certDeps] at hd'
    rcases List.mem_append.mp hd' with hroot | hD
    · rcases List.mem_append.mp hroot with hstep | hws
      · cases α with
        | none => simp [stepDeps] at hstep
        | trusted => simp [stepDeps] at hstep
        | cert β hd κ => exact ⟨_, .here, hstep⟩
      · obtain ⟨i, w', hw', hd''⟩ := mem_certDepsList hws
        have hi := lt_of_getElem?_some hw'
        obtain ⟨A, hA⟩ := getElem?_some_of_lt Cs i
          (by have := hside.lenCs; omega)
        obtain ⟨O', hO⟩ := getElem?_some_of_lt Os i
          (by have := hside.lenOs; omega)
        obtain ⟨u, hu, hmem⟩ := ihprems i w' A O' hw' hA hO d hd''
        exact ⟨u, .prem hw' hu, hmem⟩
    · obtain ⟨j, q, w', hw', hd''⟩ := mem_certDepsDis hD
      have hj := lt_of_getElem?_some hw'
      obtain ⟨A, hA⟩ := getElem?_some_of_lt DCs j
        (by have := hside.lenDCs; omega)
      obtain ⟨O', hO⟩ := getElem?_some_of_lt DOs j
        (by have := hside.lenDOs; omega)
      obtain ⟨u, hu, hmem⟩ := ihdis j q w' A O' hw' hA hO d hd''
      exact ⟨u, .dis hw' hu, hmem⟩

/-- Collection, other direction: every certificate node's reported
dependencies appear in `certDeps` of the surrounding term.  Together with
`mem_certDeps_step`, `certDeps(w)` is exactly the union of the per-node
reports (spec §6). -/
theorem certStep_deps_subset {canon : String → String}
    {Pi : RuleId → Option Rule} {reg : BackendRegistry canon}
    {w u : SupportTerm} (hstep : CertStepIn w u) :
    ∀ d, d ∈ stepDeps Pi reg u → d ∈ certDeps Pi reg w := by
  induction hstep with
  | here =>
    intro d hd'
    exact List.mem_append.mpr
      (Or.inl (List.mem_append.mpr (Or.inl hd')))
  | prem hw _ ih =>
    intro d hd'
    exact List.mem_append.mpr
      (Or.inl (List.mem_append.mpr (Or.inr (certDeps_mem_list hw (ih d hd')))))
  | dis hw _ ih =>
    intro d hd'
    exact List.mem_append.mpr (Or.inr (certDeps_mem_dis hw (ih d hd')))

/-- **Every reported premise dependency resolves to the corresponding premise
subterm of its own reporting node.** For any certificate node occurring in a
typed term, a `premise i A` entry of that node's report names the node's
`i`-th instantiated premise, and the node's `i`-th premise subterm exists and
is typed with a conclusion `≡ A` — spec §6's "resolving premise slots to the
corresponding subterms". -/
theorem certDeps_resolved {canon Pi Gamma} {reg : BackendRegistry canon}
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma (certOkOf reg) w C O) :
    ∀ rn θ ws D H β hd κ,
      CertStepIn w (.inst rn θ ws D H (.cert β hd κ)) →
      ∀ i A,
        CertDep.premise i A ∈
          stepDeps Pi reg (.inst rn θ ws D H (.cert β hd κ)) →
        ∃ w' C' O', ws[i]? = some w' ∧
          HasSupport canon Pi Gamma (certOkOf reg) w' C' O' ∧
          equiv canon C' A := by
  intro rn θ ws D H β hd κ hstep i A hmem
  obtain ⟨C₀, O₀, h₀⟩ := certStepIn_typed h _ hstep
  cases h₀ with
  | @inst _ _ _ _ _ _ r As Cs Os DCs DOs _ hside hprems hdis =>
    cases hside.assur with
    | cert hm hallow hacc =>
      obtain ⟨registered, T, hreg, hres, _⟩ := certOkOf_strict_step hacc
      have hdeps : stepDeps Pi reg (.inst rn θ ws D H (.cert β hd κ)) =
          (registered.core.uses κ).map (resolveSlot β hd As) := by
        simp [stepDeps, hside.rule, hside.prems, hreg, hres]
      rw [hdeps] at hmem
      obtain ⟨j, hj, hslot⟩ := List.mem_map.mp hmem
      cases hAsj : As[j]? with
      | none => simp [resolveSlot, hAsj] at hslot
      | some A' =>
        obtain ⟨hji, hAA⟩ : j = i ∧ A' = A := by
          simpa [resolveSlot, hAsj] using hslot
        rw [← hji, ← hAA]
        have hjlt : j < As.length := lt_of_getElem?_some hAsj
        obtain ⟨w', hw'⟩ := getElem?_some_of_lt ws j
          (by have := hside.lenAs; omega)
        obtain ⟨C', hC'⟩ := getElem?_some_of_lt Cs j
          (by have := hside.lenCs; have := hside.lenAs; omega)
        obtain ⟨O', hO'⟩ := getElem?_some_of_lt Os j
          (by have := hside.lenOs; have := hside.lenAs; omega)
        exact ⟨w', C', O', hw', hprems j w' C' O' hw' hC' hO',
          hside.premEq j C' A' hC' hAsj⟩

/-- **Every reported theory dependency names a genuine digest-addressed
entry.** For any certificate node occurring in a typed term, a
`theoryEntry β h t` in its report satisfies `t < T.length` for the theory
data `T` its `(β, h)` triple resolves to — obligation 4's validity clause
at the support level. -/
theorem certDeps_theory_valid {canon Pi Gamma} {reg : BackendRegistry canon}
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma (certOkOf reg) w C O) :
    ∀ rn θ ws D H β hd κ,
      CertStepIn w (.inst rn θ ws D H (.cert β hd κ)) →
      ∀ t,
        CertDep.theoryEntry β hd t ∈
          stepDeps Pi reg (.inst rn θ ws D H (.cert β hd κ)) →
        ∃ registered T, reg β = some registered ∧
          registered.resolveTheory hd = some T ∧ t < T.length := by
  intro rn θ ws D H β hd κ hstep t hmem
  obtain ⟨C₀, O₀, h₀⟩ := certStepIn_typed h _ hstep
  cases h₀ with
  | @inst _ _ _ _ _ _ r As Cs Os DCs DOs _ hside hprems hdis =>
    cases hside.assur with
    | cert hm hallow hacc =>
      simp only [certOkOf] at hacc
      split at hacc
      · contradiction
      · rename_i registered hreg
        split at hacc
        · contradiction
        · rename_i T hres
          have hdeps : stepDeps Pi reg (.inst rn θ ws D H (.cert β hd κ)) =
              (registered.core.uses κ).map (resolveSlot β hd As) := by
            simp [stepDeps, hside.rule, hside.prems, hreg, hres]
          rw [hdeps] at hmem
          obtain ⟨j, hj, hslot⟩ := List.mem_map.mp hmem
          cases hAsj : As[j]? with
          | some A' => simp [resolveSlot, hAsj] at hslot
          | none =>
            have ht : j - As.length = t := by
              simpa [resolveSlot, hAsj] using hslot
            have hge : As.length ≤ j := by
              rcases Nat.lt_or_ge j As.length with hlt | hge
              · obtain ⟨A', hA'⟩ := getElem?_some_of_lt As j hlt
                rw [hA'] at hAsj
                cases hAsj
              · exact hge
            have hrange :=
              registered.core.uses_valid_closed T κ
                (As.map registered.core.enc) (registered.core.enc C₀) hacc j hj
            rw [List.length_map] at hrange
            exact ⟨registered, T, hreg, hres, by omega⟩

end Lara.Support
