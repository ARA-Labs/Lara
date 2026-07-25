/-
Executable support-term checking.  The error vocabulary is symbolic and closed:
the concrete decoder may render these values, but the kernel never manufactures
free-form diagnostic strings.
-/

import Lara.Check.Error

namespace Lara.Check

open Lara Lara.Support

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

structure SupportResult where
  conclusion  : Atom
  obligations : List QuestionId
deriving DecidableEq

structure CheckedSupport (canon : String → String)
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) where
  term   : SupportTerm
  result : SupportResult
  valid  : HasSupport canon Pi Gamma (certOkOf reg) term
    result.conclusion result.obligations

/-! ### Executable side-condition helpers -/

def substDomainB (θ : Subst) (r : Rule) : Bool :=
  (θ.map Prod.fst).all (fun x => memB x r.params) &&
  r.params.all (fun x => memB x (θ.map Prod.fst))

theorem substDomainB_iff (θ : Subst) (r : Rule) :
    substDomainB θ r = true ↔
      ∀ x : VarId, x ∈ θ.map Prod.fst ↔ x ∈ r.params := by
  simp only [substDomainB, Bool.and_eq_true, List.all_eq_true, memB_iff]
  constructor
  · rintro ⟨h₁, h₂⟩ x
    exact ⟨h₁ x, h₂ x⟩
  · intro h
    exact ⟨fun x hx => (h x).mp hx, fun x hx => (h x).mpr hx⟩

def atomsEquivB (canon : String → String) : List Atom → List Atom → Bool
  | [], [] => true
  | A :: As, B :: Bs =>
      decide (equiv canon A B) && atomsEquivB canon As Bs
  | _, _ => false

def AtomsEquiv (canon : String → String) : List Atom → List Atom → Prop
  | [], [] => True
  | A :: As, B :: Bs => equiv canon A B ∧ AtomsEquiv canon As Bs
  | _, _ => False

theorem atomsEquivB_iff (canon : String → String) (As Bs : List Atom) :
    atomsEquivB canon As Bs = true ↔ AtomsEquiv canon As Bs := by
  induction As generalizing Bs with
  | nil => cases Bs <;> simp [atomsEquivB, AtomsEquiv]
  | cons A As ih =>
      cases Bs with
      | nil => simp [atomsEquivB, AtomsEquiv]
      | cons B Bs => simp [atomsEquivB, AtomsEquiv, ih]

theorem AtomsEquiv.length {canon : String → String} {As Bs : List Atom}
    (h : AtomsEquiv canon As Bs) : As.length = Bs.length := by
  induction As generalizing Bs with
  | nil => cases Bs <;> simp_all [AtomsEquiv]
  | cons A As ih =>
      cases Bs with
      | nil => simp [AtomsEquiv] at h
      | cons B Bs =>
          simp only [AtomsEquiv] at h
          simp [ih h.2]

theorem AtomsEquiv.get {canon : String → String} {As Bs : List Atom}
    (h : AtomsEquiv canon As Bs) :
    ∀ (i : Nat) (A B : Atom), As[i]? = some A → Bs[i]? = some B →
      equiv canon A B := by
  induction As generalizing Bs with
  | nil => intro i A B hA; simp at hA
  | cons A As ih =>
      cases Bs with
      | nil => simp [AtomsEquiv] at h
      | cons B Bs =>
          simp only [AtomsEquiv] at h
          intro i A' B' hA hB
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hA hB
              subst A'; subst B'
              exact h.1
          | succ j =>
              simp only [List.getElem?_cons_succ] at hA hB
              exact ih h.2 j A' B' hA hB

theorem AtomsEquiv.of_get {canon : String → String} {As Bs : List Atom}
    (hlen : As.length = Bs.length)
    (hget : ∀ (i : Nat) (A B : Atom), As[i]? = some A →
      Bs[i]? = some B → equiv canon A B) :
    AtomsEquiv canon As Bs := by
  induction As generalizing Bs with
  | nil =>
      cases Bs
      · trivial
      · simp at hlen
  | cons A As ih =>
      cases Bs with
      | nil => simp at hlen
      | cons B Bs =>
          refine ⟨hget 0 A B (by simp) (by simp), ?_⟩
          apply ih (by simpa using hlen)
          intro i A' B' hA hB
          exact hget (i + 1) A' B' (by simpa using hA) (by simpa using hB)

def strictNoQuestionB (r : Rule) (D : List (QuestionId × SupportTerm))
    (H : List QuestionId) : Bool :=
  decide (r.mode = .strict → D = [] ∧ H = [])

theorem strictNoQuestionB_iff (r : Rule)
    (D : List (QuestionId × SupportTerm)) (H : List QuestionId) :
    strictNoQuestionB r D H = true ↔
      (r.mode = .strict → D = [] ∧ H = []) := by
  exact decide_eq_true_iff

def assuranceOkB {canon : String → String} (reg : BackendRegistry canon)
    (r : Rule) (As : List Atom) (C : Atom) : Assurance → Bool
  | .none => decide (r.mode = .defeasible)
  | .trusted => decide (r.mode = .strict) && decide (r.allowTrusted = true)
  | .cert β h κ =>
      decide (r.mode = .strict) &&
      decide ((β, h) ∈ r.certifiers) &&
      certOkBOf reg β h κ As C

theorem assuranceOkB_iff {canon : String → String}
    (reg : BackendRegistry canon) (r : Rule) (As : List Atom) (C : Atom)
    (α : Assurance) :
    assuranceOkB reg r As C α = true ↔
      AssuranceOk (certOkOf reg) r As C α := by
  cases α with
  | none =>
      simp [assuranceOkB]
      exact ⟨fun h => .defeasible h, fun h => by cases h; assumption⟩
  | trusted =>
      simp only [assuranceOkB, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨fun h => .trusted h.1 h.2, fun h => by cases h; simp_all⟩
  | cert β hd κ =>
      simp only [assuranceOkB, Bool.and_eq_true, decide_eq_true_eq,
        certOkBOf_iff]
      exact ⟨fun h => .cert h.1.1 h.1.2 h.2, fun h => by cases h; simp_all⟩

/- Answer checking is deliberately separate from D/H accounting: this pins the
validation precedence and lets failures identify the exact question location. -/
def answerOkB (canon : String → String) (θ : Subst) (questions : List Question)
    (q : QuestionId) (A : Atom) : Bool :=
  questions.any (fun qd =>
    decide (qd.name = q) &&
      match instAPat θ qd.answer with
      | none => false
      | some Aq => decide (equiv canon A Aq))

theorem answerOkB_iff (canon : String → String) (θ : Subst)
    (questions : List Question) (q : QuestionId) (A : Atom) :
    answerOkB canon θ questions q A = true ↔
      ∃ qd, qd ∈ questions ∧ qd.name = q ∧
        ∃ Aq, instAPat θ qd.answer = some Aq ∧ equiv canon A Aq := by
  simp only [answerOkB, List.any_eq_true]
  constructor
  · rintro ⟨qd, hmem, hqd⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hqd
    rcases hqd with ⟨hname, hinst⟩
    split at hinst
    · contradiction
    · rename_i Aq heq
      simp only [decide_eq_true_eq] at hinst
      exact ⟨qd, hmem, hname, Aq, heq, hinst⟩
  · rintro ⟨qd, hmem, hname, Aq, hinst, heq⟩
    refine ⟨qd, hmem, ?_⟩
    simp [hname, hinst, heq]

def answersOkB (canon : String → String) (θ : Subst)
    (questions : List Question) :
    List (QuestionId × SupportTerm) → List SupportResult → Bool
  | [], [] => true
  | (q, _) :: D, result :: results =>
      answerOkB canon θ questions q result.conclusion &&
      answersOkB canon θ questions D results
  | _, _ => false

/- The answer pass precedes discharge accounting so answer mismatches retain
their frozen R6 priority.  Unknown discharge keys are deliberately skipped
here: the later accounting pass reports them as R5. -/
def knownAnswersOkB (canon : String → String) (θ : Subst)
    (questions : List Question) :
    List (QuestionId × SupportTerm) → List SupportResult → Bool
  | [], [] => true
  | (q, _) :: D, result :: results =>
      (if memB q (questions.map (·.name)) then
          answerOkB canon θ questions q result.conclusion
        else true) &&
      knownAnswersOkB canon θ questions D results
  | _, _ => false

def AnswersOk (canon : String → String) (θ : Subst)
    (questions : List Question) :
    List (QuestionId × SupportTerm) → List SupportResult → Prop
  | [], [] => True
  | (q, _) :: D, result :: results =>
      (∃ qd, qd ∈ questions ∧ qd.name = q ∧
        ∃ Aq, instAPat θ qd.answer = some Aq ∧
          equiv canon result.conclusion Aq) ∧
      AnswersOk canon θ questions D results
  | _, _ => False

theorem answersOkB_iff (canon : String → String) (θ : Subst)
    (questions : List Question) (D : List (QuestionId × SupportTerm))
    (results : List SupportResult) :
    answersOkB canon θ questions D results = true ↔
      AnswersOk canon θ questions D results := by
  induction D generalizing results with
  | nil => cases results <;> simp [answersOkB, AnswersOk]
  | cons qw D ih =>
      obtain ⟨q, w⟩ := qw
      cases results with
      | nil => simp [answersOkB, AnswersOk]
      | cons result results =>
          simp [answersOkB, AnswersOk, answerOkB_iff, ih]

theorem knownAnswersOkB_eq_answersOkB (canon : String → String) (θ : Subst)
    (questions : List Question) (D : List (QuestionId × SupportTerm))
    (results : List SupportResult)
    (hkeys : ∀ n, n ∈ D.map Prod.fst → n ∈ questions.map (·.name)) :
    knownAnswersOkB canon θ questions D results =
      answersOkB canon θ questions D results := by
  induction D generalizing results with
  | nil => cases results <;> simp [knownAnswersOkB, answersOkB]
  | cons qw D ih =>
      obtain ⟨q, w⟩ := qw
      cases results with
      | nil => simp [knownAnswersOkB, answersOkB]
      | cons result results =>
          have hq : memB q (questions.map (·.name)) = true :=
            memB_iff.mpr (hkeys q (by simp))
          have ht : ∀ n, n ∈ D.map Prod.fst →
              n ∈ questions.map (·.name) := by
            intro n hn
            exact hkeys n (by simp [hn])
          simp [knownAnswersOkB, answersOkB, hq, ih results ht]

theorem AnswersOk.length {canon : String → String} {θ : Subst}
    {questions : List Question} {D : List (QuestionId × SupportTerm)}
    {results : List SupportResult}
    (h : AnswersOk canon θ questions D results) :
    results.length = D.length := by
  induction D generalizing results with
  | nil => cases results <;> simp_all [AnswersOk]
  | cons qw D ih =>
      cases results with
      | nil => simp [AnswersOk] at h
      | cons result results =>
          simp only [AnswersOk] at h
          simp [ih h.2]

theorem AnswersOk.get {canon : String → String} {θ : Subst}
    {questions : List Question} {D : List (QuestionId × SupportTerm)}
    {results : List SupportResult}
    (h : AnswersOk canon θ questions D results) :
    ∀ (j : Nat) (q : QuestionId) (w : SupportTerm) (A : Atom),
      D[j]? = some (q, w) → (results.map (·.conclusion))[j]? = some A →
      ∃ qd, qd ∈ questions ∧ qd.name = q ∧
        ∃ Aq, instAPat θ qd.answer = some Aq ∧ equiv canon A Aq := by
  induction D generalizing results with
  | nil => intro j q w A hD; simp at hD
  | cons qw D ih =>
      obtain ⟨q₀, w₀⟩ := qw
      cases results with
      | nil => simp [AnswersOk] at h
      | cons result results =>
          simp only [AnswersOk] at h
          intro j q w A hD hA
          cases j with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq,
                List.map_cons] at hD hA
              injection hD with hq hw
              subst q; subst w
              subst A
              exact h.1
          | succ j =>
              simp only [List.getElem?_cons_succ, List.map_cons] at hD hA
              exact ih h.2 j q w A hD hA

theorem AnswersOk.of_get {canon : String → String} {θ : Subst}
    {questions : List Question} {D : List (QuestionId × SupportTerm)}
    {results : List SupportResult}
    (hlen : results.length = D.length)
    (hget : ∀ (j : Nat) (q : QuestionId) (w : SupportTerm) (A : Atom),
      D[j]? = some (q, w) → (results.map (·.conclusion))[j]? = some A →
      ∃ qd, qd ∈ questions ∧ qd.name = q ∧
        ∃ Aq, instAPat θ qd.answer = some Aq ∧ equiv canon A Aq) :
    AnswersOk canon θ questions D results := by
  induction D generalizing results with
  | nil =>
      cases results
      · trivial
      · simp at hlen
  | cons qw D ih =>
      obtain ⟨q, w⟩ := qw
      cases results with
      | nil => simp at hlen
      | cons result results =>
          refine ⟨hget 0 q w result.conclusion (by simp) (by simp), ?_⟩
          apply ih (by simpa using hlen)
          intro j q' w' A hD hA
          exact hget (j + 1) q' w' A (by simpa using hD) (by simpa using hA)

/-! ### Recursive inference -/

private def firstPremiseMismatch (canon : String → String) :
    Nat → List Atom → List Atom → Option (Nat × Atom × Atom)
  | _, [], [] => none
  | i, A :: As, B :: Bs =>
      if equiv canon A B then firstPremiseMismatch canon (i + 1) As Bs
      else some (i, B, A)
  | _, _, _ => none

private def firstBadAnswer (canon : String → String) (θ : Subst)
    (questions : List Question) :
    List (QuestionId × SupportTerm) → List SupportResult →
      Option (QuestionId × DischargeReason)
  | [], [] => none
  | (q, _) :: D, result :: results =>
      match questions.find? (fun qd => qd.name = q) with
      | none => firstBadAnswer canon θ questions D results
      | some qd =>
          match instAPat θ qd.answer with
          | none => some (q, .answerInstantiation q qd.answer)
          | some Aq =>
              if equiv canon result.conclusion Aq then
                firstBadAnswer canon θ questions D results
              else some (q, .conclusionMismatch q Aq result.conclusion)
  | _, _ => none

def requireB (ok : Bool) (err : CheckError) :
    Except CheckError Unit :=
  if ok then .ok () else .error err

def premiseError (canon : String → String) (loc : CheckLoc)
    (expected actual : List Atom) : CheckError :=
  match firstPremiseMismatch canon 0 actual expected with
  | some (i, expected, actual) =>
      .R4 (.premise loc i) (.mismatch expected actual)
  | none => .R4 loc (.count expected.length actual.length)

def answerError (canon : String → String) (θ : Subst)
    (questions : List Question) (D : List (QuestionId × SupportTerm))
    (results : List SupportResult) (loc : CheckLoc) (fallback : APat) :
    CheckError :=
  match firstBadAnswer canon θ questions D results with
  | some (q, reason) => .R6 (.question loc q) reason
  | none => .R6 loc (.answerInstantiation
      ((D.map Prod.fst).headD ⟨""⟩) fallback)

def assuranceError (reg : BackendRegistry canon) (r : Rule)
    (α : Assurance) (loc : CheckLoc) :
    CheckError :=
  match α with
  | .none => .R7 loc (.wrongMode r.mode α)
  | .trusted =>
      if r.mode = .strict then .R7 loc .trustedDisallowed
      else .R7 loc (.wrongMode r.mode α)
  | .cert β hd κ =>
      if r.mode ≠ .strict then .R7 loc (.wrongMode r.mode α)
      else if (β, hd) ∉ r.certifiers then
        .R7 loc (.certifierUnallowlisted β hd)
      else
        match reg β with
        | none => .R13 loc (.backendMissing β)
        | some registered =>
            match registered.resolve hd with
            | none => .R13 loc (.digestMissing β hd)
            | some _ => .R13 loc (.replayRejected β hd κ)

/- The public program erases proof witnesses. Keeping this recursion plainly
first-order gives Lean's code generator a compact executable; its relational
soundness and completeness certificate is proved in `SupportProof`. -/
mutual
  def inferSupportRaw {canon : String → String}
      (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
      (reg : BackendRegistry canon) (w : SupportTerm) (loc : CheckLoc) :
      Except CheckError SupportResult :=
    match w with
    | .leaf l =>
        match Gamma l with
        | none => .error (.R1 loc (.missingLeaf l))
        | some C => .ok ⟨C, []⟩
    | .inst rn θ ws D H α => do
        let r ← match Pi rn with
          | none => .error (.R1 loc (.missingRule rn))
          | some r => .ok r
        requireB (decide (θ.map Prod.fst).Nodup)
          (.R3 loc (.duplicateKeys (θ.map Prod.fst)))
        requireB (substDomainB θ r)
          (.R3 loc (.domainMismatch (θ.map Prod.fst) r.params))
        let As ← match instAPats θ r.premises with
          | none => .error (.R3 loc (.premiseInstantiation r.premises))
          | some As => .ok As
        let C ← match instAPat θ r.concl with
          | none => .error (.R3 loc (.conclusionInstantiation r.concl))
          | some C => .ok C
        let premiseResults ← inferPremisesRaw Pi Gamma reg ws loc 0
        let dischargeResults ← inferDischargesRaw Pi Gamma reg D loc
        requireB (decide (premiseResults.length = As.length))
          (.R4 loc (.count As.length premiseResults.length))
        requireB (atomsEquivB canon (premiseResults.map (·.conclusion)) As)
          (premiseError canon loc As (premiseResults.map (·.conclusion)))
        requireB (knownAnswersOkB canon θ r.questions D dischargeResults)
          (answerError canon θ r.questions D dischargeResults loc r.concl)
        let dkeys := D.map Prod.fst
        let qnames := questionNames r
        requireB (decide qnames.Nodup)
          (.R5 loc (.duplicateDeclarations qnames))
        requireB (decide dkeys.Nodup)
          (.R5 loc (.duplicateDischarges dkeys))
        requireB (decide H.Nodup) (.R5 loc (.duplicateHoles H))
        requireB (decide (∀ qd, qd ∈ r.questions →
            qd.name ∈ dkeys ∨ qd.name ∈ H))
          (.R5 loc (.uncovered qnames dkeys H))
        requireB (decide (∀ n, n ∈ dkeys → n ∉ H))
          (.R5 loc (.overlap dkeys H))
        requireB (decide (∀ n, n ∈ dkeys → n ∈ qnames))
          (.R5 loc (.undeclaredDischarge dkeys qnames))
        requireB (decide (∀ n, n ∈ H → n ∈ qnames))
          (.R5 loc (.undeclaredHole H qnames))
        requireB (strictNoQuestionB r D H)
          (.R7 loc (.questionsPresent dkeys H))
        requireB (assuranceOkB reg r As C α)
          (assuranceError reg r α loc)
        pure ⟨C, collectObligations
          (premiseResults.map (·.obligations))
          (dischargeResults.map (·.obligations)) r H⟩

  def inferPremisesRaw {canon : String → String}
      (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
      (reg : BackendRegistry canon) (ws : List SupportTerm) (loc : CheckLoc)
      (i : Nat) : Except CheckError (List SupportResult) :=
    match ws with
    | [] => .ok []
    | w :: ws => do
        let result ← inferSupportRaw Pi Gamma reg w (.premise loc i)
        let results ← inferPremisesRaw Pi Gamma reg ws loc (i + 1)
        pure (result :: results)

  def inferDischargesRaw {canon : String → String}
      (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
      (reg : BackendRegistry canon) (D : List (QuestionId × SupportTerm))
      (loc : CheckLoc) : Except CheckError (List SupportResult) :=
    match D with
    | [] => .ok []
    | (q, w) :: D => do
        let result ← inferSupportRaw Pi Gamma reg w (.question loc q)
        let results ← inferDischargesRaw Pi Gamma reg D loc
        pure (result :: results)
end

def inferSupport {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (loc : CheckLoc)
    (w : SupportTerm) : Except CheckError SupportResult :=
  inferSupportRaw Pi Gamma reg w loc


end Lara.Check
