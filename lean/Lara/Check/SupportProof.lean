import Lara.Check.Support

namespace Lara.Check

open Lara Lara.Support

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/- This proof-only module intentionally mirrors `inferSupportRaw`'s staged
`Except` binds. The explicit branch order witnesses the executable checker's
frozen diagnostic precedence while keeping proof terms out of generated code. -/

private theorem requireB_sound {b : Bool} {e : CheckError}
    (h : requireB b e = .ok ()) : b = true := by
  cases b <;> simp_all [requireB]

mutual
  private theorem inferSupportRaw_sound {canon : String → String}
      (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
      (reg : BackendRegistry canon) (w : SupportTerm) (loc : CheckLoc)
      (result : SupportResult)
      (h : inferSupportRaw Pi Gamma reg w loc = .ok result) :
      HasSupport canon Pi Gamma (certOkOf reg) w
        result.conclusion result.obligations := by
    cases w with
    | leaf l =>
        simp only [inferSupportRaw] at h
        split at h
        · simp at h
        · rename_i C hΓ
          simp only [Except.ok.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact .leaf hΓ
    | inst rn θ ws D H α =>
        simp only [inferSupportRaw, Bind.bind, Except.bind, Pure.pure,
          Except.pure] at h
        cases hr : Pi rn with
        | none => simp [hr] at h
        | some r =>
          simp only [hr] at h
          cases hn : requireB (decide (θ.map Prod.fst).Nodup)
              (.R3 loc (.duplicateKeys (θ.map Prod.fst))) with
          | error e => simp [hn] at h
          | ok u =>
            have hu : u = () := Subsingleton.elim _ _
            subst u
            simp only [hn] at h
            cases hdom : requireB (substDomainB θ r)
                (.R3 loc (.domainMismatch (θ.map Prod.fst) r.params)) with
            | error e => simp [hdom] at h
            | ok u =>
              have hu : u = () := Subsingleton.elim _ _
              subst u
              simp only [hdom] at h
              cases hAs : instAPats θ r.premises with
              | none => simp [hAs] at h
              | some As =>
                simp only [hAs] at h
                cases hC : instAPat θ r.concl with
                | none => simp [hC] at h
                | some C =>
                  simp only [hC] at h
                  cases hp : inferPremisesRaw Pi Gamma reg ws loc 0 with
                  | error e => simp [hp] at h
                  | ok ps =>
                    simp only [hp] at h
                    cases hd : inferDischargesRaw Pi Gamma reg D loc with
                    | error e => simp [hd] at h
                    | ok ds =>
                      simp only [hd] at h
                      cases hlen : requireB (decide (ps.length = As.length))
                          (.R4 loc (.count As.length ps.length)) with
                      | error e => simp [hlen] at h
                      | ok u =>
                        have hu : u = () := Subsingleton.elim _ _
                        subst u
                        simp only [hlen] at h
                        cases heqv : requireB
                            (atomsEquivB canon (ps.map (·.conclusion)) As)
                            (Lara.Check.premiseError canon loc As
                              (ps.map (·.conclusion))) with
                        | error e => simp [heqv] at h
                        | ok u =>
                          have hu : u = () := Subsingleton.elim _ _
                          subst u
                          simp only [heqv] at h
                          have hans : requireB
                              (knownAnswersOkB canon θ r.questions D ds)
                              (Lara.Check.answerError canon θ r.questions D ds
                                loc r.concl) = .ok () := by
                            cases hx : requireB
                                (knownAnswersOkB canon θ r.questions D ds)
                                (Lara.Check.answerError canon θ r.questions D ds
                                  loc r.concl) with
                            | error e => simp [hx] at h
                            | ok u =>
                              have hu : u = () := Subsingleton.elim _ _
                              subst u
                              rfl
                          simp only [hans] at h
                          cases hqn : requireB (decide (questionNames r).Nodup)
                              (.R5 loc (.duplicateDeclarations
                                (questionNames r))) with
                          | error e => simp [hqn] at h
                          | ok u =>
                            have hu : u = () := Subsingleton.elim _ _
                            subst u
                            simp only [hqn] at h
                            cases hdn : requireB
                                (decide (D.map Prod.fst).Nodup)
                                (.R5 loc (.duplicateDischarges
                                  (D.map Prod.fst))) with
                            | error e => simp [hdn] at h
                            | ok u =>
                              have hu : u = () := Subsingleton.elim _ _
                              subst u
                              simp only [hdn] at h
                              cases hhn : requireB (decide H.Nodup)
                                  (.R5 loc (.duplicateHoles H)) with
                              | error e => simp [hhn] at h
                              | ok u =>
                                have hu : u = () := Subsingleton.elim _ _
                                subst u
                                simp only [hhn] at h
                                cases hcover : requireB (decide
                                    (∀ qd, qd ∈ r.questions →
                                      qd.name ∈ D.map Prod.fst ∨
                                        qd.name ∈ H))
                                    (.R5 loc (.uncovered
                                      (questionNames r) (D.map Prod.fst) H)) with
                                | error e => simp [hcover] at h
                                | ok u =>
                                  have hu : u = () := Subsingleton.elim _ _
                                  subst u
                                  simp only [hcover] at h
                                  cases hdisj : requireB (decide
                                      (∀ n, n ∈ D.map Prod.fst → n ∉ H))
                                      (.R5 loc (.overlap (D.map Prod.fst) H)) with
                                  | error e => simp [hdisj] at h
                                  | ok u =>
                                    have hu : u = () := Subsingleton.elim _ _
                                    subst u
                                    simp only [hdisj] at h
                                    cases hkd : requireB (decide
                                        (∀ n, n ∈ D.map Prod.fst →
                                          n ∈ questionNames r))
                                        (.R5 loc (.undeclaredDischarge
                                          (D.map Prod.fst)
                                          (questionNames r))) with
                                    | error e => simp [hkd] at h
                                    | ok u =>
                                      have hu : u = () := Subsingleton.elim _ _
                                      subst u
                                      simp only [hkd] at h
                                      cases hkh : requireB (decide
                                          (∀ n, n ∈ H →
                                            n ∈ questionNames r))
                                          (.R5 loc (.undeclaredHole H
                                            (questionNames r))) with
                                      | error e => simp [hkh] at h
                                      | ok u =>
                                        have hu : u = () :=
                                          Subsingleton.elim _ _
                                        subst u
                                        simp only [hkh] at h
                                        cases hstrict : requireB
                                              (strictNoQuestionB r D H)
                                              (.R7 loc (.questionsPresent
                                                (D.map Prod.fst) H)) with
                                          | error e => simp [hstrict] at h
                                          | ok u =>
                                            have hu : u = () :=
                                              Subsingleton.elim _ _
                                            subst u
                                            simp only [hstrict] at h
                                            cases hassur : requireB
                                                (assuranceOkB reg r As C α)
                                                (Lara.Check.assuranceError reg r
                                                  α loc) with
                                            | error e => simp [hassur] at h
                                            | ok u =>
                                              have hu : u = () :=
                                                Subsingleton.elim _ _
                                              subst u
                                              simp only [hassur,
                                                Except.ok.injEq] at h
                                              subst result
                                              have hps :=
                                                inferPremisesRaw_sound Pi Gamma
                                                  reg ws loc 0 ps hp
                                              have hds :=
                                                inferDischargesRaw_sound Pi Gamma
                                                  reg D loc ds hd
                                              have hkeysD :
                                                  ∀ n,
                                                    n ∈ D.map Prod.fst →
                                                    n ∈ questionNames r :=
                                                decide_eq_true_eq.mp
                                                  (requireB_sound hkd)
                                              apply HasSupport.inst
                                                (r := r) (As := As)
                                                (Cs := ps.map (·.conclusion))
                                                (Os := ps.map (·.obligations))
                                                (DCs := ds.map (·.conclusion))
                                                (DOs := ds.map (·.obligations))
                                              · exact {
                                                  rule := hr
                                                  θNodup := decide_eq_true_eq.mp
                                                    (requireB_sound hn)
                                                  θDom :=
                                                    (substDomainB_iff θ r).mp
                                                      (requireB_sound hdom)
                                                  prems := hAs
                                                  concl := hC
                                                  lenAs := hps.1.symm.trans
                                                    (decide_eq_true_eq.mp
                                                      (requireB_sound hlen))
                                                  lenCs := by simpa using hps.1
                                                  lenOs := by simpa using hps.1
                                                  premEq :=
                                                    (AtomsEquiv.get
                                                      ((atomsEquivB_iff canon
                                                        _ _).mp
                                                        (requireB_sound heqv)))
                                                  lenDCs := by simpa using hds.1
                                                  lenDOs := by simpa using hds.1
                                                  ans := AnswersOk.get
                                                    ((answersOkB_iff canon θ
                                                      r.questions D ds).mp
                                                      (by
                                                        rw [←
                                                          knownAnswersOkB_eq_answersOkB
                                                            canon θ r.questions
                                                            D ds (by
                                                              simpa
                                                                [questionNames]
                                                              using hkeysD)]
                                                        exact
                                                          requireB_sound hans))
                                                  qNodup :=
                                                    decide_eq_true_eq.mp
                                                      (requireB_sound hqn)
                                                  dNodup :=
                                                    decide_eq_true_eq.mp
                                                      (requireB_sound hdn)
                                                  hNodup :=
                                                    decide_eq_true_eq.mp
                                                      (requireB_sound hhn)
                                                  cover :=
                                                    decide_eq_true_eq.mp
                                                      (requireB_sound hcover)
                                                  disj :=
                                                    decide_eq_true_eq.mp
                                                      (requireB_sound hdisj)
                                                  keysD :=
                                                    hkeysD
                                                  keysH :=
                                                    decide_eq_true_eq.mp
                                                      (requireB_sound hkh)
                                                  strictNoQ :=
                                                    (strictNoQuestionB_iff
                                                      r D H).mp
                                                      (requireB_sound hstrict)
                                                  assur :=
                                                    (assuranceOkB_iff reg r
                                                      As C α).mp
                                                      (requireB_sound hassur) }
                                              · intro i w' A O hw hA hO
                                                cases hx : ps[i]? with
                                                | none => simp [hx] at hA
                                                | some x =>
                                                  have hc : x.conclusion = A := by
                                                    simpa [hx] using hA
                                                  have ho : x.obligations = O := by
                                                    simpa [hx] using hO
                                                  cases x
                                                  simp_all only
                                                  exact hps.2 i w'
                                                    ⟨A, O⟩ hw hx
                                              · intro j q w' A O hw hA hO
                                                cases hx : ds[j]? with
                                                | none => simp [hx] at hA
                                                | some x =>
                                                  have hc : x.conclusion = A := by
                                                    simpa [hx] using hA
                                                  have ho : x.obligations = O := by
                                                    simpa [hx] using hO
                                                  cases x
                                                  simp_all only
                                                  exact hds.2 j q w'
                                                    ⟨A, O⟩ hw hx

  private theorem inferPremisesRaw_sound {canon : String → String}
      (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
      (reg : BackendRegistry canon) (ws : List SupportTerm)
      (loc : CheckLoc) (start : Nat) (results : List SupportResult)
      (h : inferPremisesRaw Pi Gamma reg ws loc start = .ok results) :
      results.length = ws.length ∧
      ∀ (i : Nat) (w : SupportTerm) (result : SupportResult),
        ws[i]? = some w → results[i]? = some result →
        HasSupport canon Pi Gamma (certOkOf reg) w
          result.conclusion result.obligations := by
    cases ws with
    | nil => simp [inferPremisesRaw] at h; subst results; simp
    | cons w ws =>
        simp only [inferPremisesRaw] at h
        cases hh : inferSupportRaw Pi Gamma reg w (.premise loc start) with
        | error e =>
            simp [hh, Bind.bind, Except.bind] at h
        | ok head =>
            cases ht : inferPremisesRaw Pi Gamma reg ws loc (start + 1) with
            | error e =>
                simp [hh, ht, Bind.bind, Except.bind] at h
            | ok tail =>
                simp [hh, ht, Bind.bind, Pure.pure, Except.bind,
                  Except.pure] at h
                subst results
                have hhead := inferSupportRaw_sound Pi Gamma reg w
                  (.premise loc start) head hh
                have htail := inferPremisesRaw_sound Pi Gamma reg ws loc
                  (start + 1) tail ht
                refine ⟨by simp [htail.1], ?_⟩
                intro i w' result hw hr
                cases i with
                | zero =>
                    simp only [List.getElem?_cons_zero,
                      Option.some.injEq] at hw hr
                    subst w'; subst result
                    exact hhead
                | succ i =>
                    simp only [List.getElem?_cons_succ] at hw hr
                    exact htail.2 i w' result hw hr

  private theorem inferDischargesRaw_sound {canon : String → String}
      (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
      (reg : BackendRegistry canon) (D : List (QuestionId × SupportTerm))
      (loc : CheckLoc) (results : List SupportResult)
      (h : inferDischargesRaw Pi Gamma reg D loc = .ok results) :
      results.length = D.length ∧
      ∀ (j : Nat) (q : QuestionId) (w : SupportTerm)
        (result : SupportResult), D[j]? = some (q, w) →
        results[j]? = some result →
        HasSupport canon Pi Gamma (certOkOf reg) w
          result.conclusion result.obligations := by
    cases D with
    | nil => simp [inferDischargesRaw] at h; subst results; simp
    | cons qw D =>
        obtain ⟨q, w⟩ := qw
        simp only [inferDischargesRaw] at h
        cases hh : inferSupportRaw Pi Gamma reg w (.question loc q) with
        | error e =>
            simp [hh, Bind.bind, Except.bind] at h
        | ok head =>
            cases ht : inferDischargesRaw Pi Gamma reg D loc with
            | error e =>
                simp [hh, ht, Bind.bind, Except.bind] at h
            | ok tail =>
                simp [hh, ht, Bind.bind, Pure.pure, Except.bind,
                  Except.pure] at h
                subst results
                have hhead := inferSupportRaw_sound Pi Gamma reg w
                  (.question loc q) head hh
                have htail := inferDischargesRaw_sound Pi Gamma reg D loc
                  tail ht
                refine ⟨by simp [htail.1], ?_⟩
                intro j q' w' result hD hr
                cases j with
                | zero =>
                    simp only [List.getElem?_cons_zero,
                      Option.some.injEq] at hD hr
                    injection hD with hq hw
                    subst q'; subst w'; subst result
                    exact hhead
                | succ j =>
                    simp only [List.getElem?_cons_succ] at hD hr
                    exact htail.2 j q' w' result hD hr
end

theorem inferSupport_sound {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {loc : CheckLoc} {w : SupportTerm}
    {result : SupportResult}
    (h : inferSupport Pi Gamma reg loc w = .ok result) :
    HasSupport canon Pi Gamma (certOkOf reg) w
      result.conclusion result.obligations :=
  inferSupportRaw_sound Pi Gamma reg w loc result h

private def zipResults : List Atom → List (List QuestionId) →
    List SupportResult
  | [], [] => []
  | C :: Cs, O :: Os => ⟨C, O⟩ :: zipResults Cs Os
  | _, _ => []

private theorem zipResults_conclusions :
    ∀ {Cs : List Atom} {Os : List (List QuestionId)},
      Cs.length = Os.length →
      (zipResults Cs Os).map (·.conclusion) = Cs := by
  intro Cs
  induction Cs with
  | nil => intro Os h; cases Os <;> simp_all [zipResults]
  | cons C Cs ih =>
      intro Os h
      cases Os with
      | nil => simp at h
      | cons O Os => simp [zipResults, ih (by simpa using h)]

private theorem zipResults_obligations :
    ∀ {Cs : List Atom} {Os : List (List QuestionId)},
      Cs.length = Os.length →
      (zipResults Cs Os).map (·.obligations) = Os := by
  intro Cs
  induction Cs with
  | nil => intro Os h; cases Os <;> simp_all [zipResults]
  | cons C Cs ih =>
      intro Os h
      cases Os with
      | nil => simp at h
      | cons O Os => simp [zipResults, ih (by simpa using h)]

private theorem inferPremisesRaw_complete {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (loc : CheckLoc) :
    ∀ (ws : List SupportTerm) (Cs : List Atom)
      (Os : List (List QuestionId)) (start : Nat),
      Cs.length = ws.length → Os.length = ws.length →
      (∀ (i : Nat) (w : SupportTerm) (A : Atom) (O : List QuestionId),
        ws[i]? = some w → Cs[i]? = some A → Os[i]? = some O →
        inferSupportRaw Pi Gamma reg w (.premise loc (start + i)) =
          .ok ⟨A, O⟩) →
      inferPremisesRaw Pi Gamma reg ws loc start =
        .ok (zipResults Cs Os) := by
  intro ws
  induction ws with
  | nil =>
      intro Cs Os start hCs hOs _
      cases Cs <;> cases Os <;> simp_all [inferPremisesRaw, zipResults]
  | cons w ws ih =>
      intro Cs Os start hCs hOs hall
      cases Cs with
      | nil => simp at hCs
      | cons A Cs =>
          cases Os with
          | nil => simp at hOs
          | cons O Os =>
              have hhead := hall 0 w A O (by simp) (by simp) (by simp)
              have htail :
                  ∀ (i : Nat) (w' : SupportTerm) (A' : Atom)
                    (O' : List QuestionId), ws[i]? = some w' →
                    Cs[i]? = some A' → Os[i]? = some O' →
                    inferSupportRaw Pi Gamma reg w'
                      (.premise loc ((start + 1) + i)) =
                        .ok ⟨A', O'⟩ := by
                intro i w' A' O' hw hA hO
                have hh := hall (i + 1) w' A' O'
                  (by simpa using hw) (by simpa using hA) (by simpa using hO)
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
              have ht := ih Cs Os (start + 1) (by simpa using hCs)
                (by simpa using hOs) htail
              have hhead' : inferSupportRaw Pi Gamma reg w
                  (.premise loc start) = .ok ⟨A, O⟩ := by
                simpa using hhead
              simp [inferPremisesRaw, zipResults, hhead', ht,
                Bind.bind, Pure.pure, Except.bind, Except.pure]

private theorem inferDischargesRaw_complete {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (loc : CheckLoc) :
    ∀ (D : List (QuestionId × SupportTerm)) (Cs : List Atom)
      (Os : List (List QuestionId)),
      Cs.length = D.length → Os.length = D.length →
      (∀ (j : Nat) (q : QuestionId) (w : SupportTerm) (A : Atom)
        (O : List QuestionId), D[j]? = some (q, w) →
        Cs[j]? = some A → Os[j]? = some O →
        inferSupportRaw Pi Gamma reg w (.question loc q) =
          .ok ⟨A, O⟩) →
      inferDischargesRaw Pi Gamma reg D loc =
        .ok (zipResults Cs Os) := by
  intro D
  induction D with
  | nil =>
      intro Cs Os hCs hOs _
      cases Cs <;> cases Os <;> simp_all [inferDischargesRaw, zipResults]
  | cons qw D ih =>
      obtain ⟨q, w⟩ := qw
      intro Cs Os hCs hOs hall
      cases Cs with
      | nil => simp at hCs
      | cons A Cs =>
          cases Os with
          | nil => simp at hOs
          | cons O Os =>
              have hhead := hall 0 q w A O (by simp) (by simp) (by simp)
              have htail :
                  ∀ (j : Nat) (q' : QuestionId) (w' : SupportTerm)
                    (A' : Atom) (O' : List QuestionId),
                    D[j]? = some (q', w') → Cs[j]? = some A' →
                    Os[j]? = some O' →
                    inferSupportRaw Pi Gamma reg w' (.question loc q') =
                      .ok ⟨A', O'⟩ := by
                intro j q' w' A' O' hD hA hO
                exact hall (j + 1) q' w' A' O'
                  (by simpa using hD) (by simpa using hA) (by simpa using hO)
              have ht := ih Cs Os (by simpa using hCs)
                (by simpa using hOs) htail
              simp [inferDischargesRaw, zipResults, hhead, ht,
                Bind.bind, Pure.pure, Except.bind, Except.pure]

theorem inferSupport_complete {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {w : SupportTerm} {C : Atom}
    {O : List QuestionId}
    (h : HasSupport canon Pi Gamma (certOkOf reg) w C O) :
    ∀ loc, inferSupport Pi Gamma reg loc w = .ok ⟨C, O⟩ := by
  induction h with
  | leaf hΓ =>
      intro loc
      simp [inferSupport, inferSupportRaw, hΓ]
  | @inst rn θ ws D H α r As Cs Os DCs DOs C hside hprems hdis
      ihprems ihdis =>
      intro loc
      have hp := inferPremisesRaw_complete Pi Gamma reg loc ws Cs Os 0
        hside.lenCs hside.lenOs (by
          intro i w A O hw hA hO
          simpa [inferSupport] using
            ihprems i w A O hw hA hO (.premise loc i))
      have hd := inferDischargesRaw_complete Pi Gamma reg loc D DCs DOs
        hside.lenDCs hside.lenDOs (by
          intro j q w A O hD hA hO
          simpa [inferSupport] using
            ihdis j q w A O hD hA hO (.question loc q))
      have hCO : Cs.length = Os.length :=
        hside.lenCs.trans hside.lenOs.symm
      have hDCO : DCs.length = DOs.length :=
        hside.lenDCs.trans hside.lenDOs.symm
      have hpremB : atomsEquivB canon
          ((zipResults Cs Os).map (·.conclusion)) As = true := by
        apply (atomsEquivB_iff canon _ _).mpr
        rw [zipResults_conclusions hCO]
        exact AtomsEquiv.of_get
          (hside.lenCs.trans hside.lenAs) hside.premEq
      have hansB : answersOkB canon θ r.questions D
          (zipResults DCs DOs) = true := by
        apply (answersOkB_iff canon θ r.questions D _).mpr
        apply AnswersOk.of_get
        · have hz := congrArg List.length (zipResults_conclusions hDCO)
          simp only [List.length_map] at hz
          exact hz.trans hside.lenDCs
        · intro j q w A hDj hA
          apply hside.ans j q w A hDj
          rw [← zipResults_conclusions hDCO]
          exact hA
      have hknownB : knownAnswersOkB canon θ r.questions D
          (zipResults DCs DOs) = true := by
        rw [knownAnswersOkB_eq_answersOkB canon θ r.questions D
          (zipResults DCs DOs) (by
            simpa [questionNames] using hside.keysD)]
        exact hansB
      have hdomB := (substDomainB_iff θ r).mpr hside.θDom
      have hstrictB := (strictNoQuestionB_iff r D H).mpr hside.strictNoQ
      have hassurB := (assuranceOkB_iff reg r As C α).mpr hside.assur
      have hcoverB : decide (∀ qd, qd ∈ r.questions →
          qd.name ∈ D.map Prod.fst ∨ qd.name ∈ H) = true :=
        decide_eq_true_eq.mpr hside.cover
      have hdisjB : decide (∀ n, n ∈ D.map Prod.fst → n ∉ H) = true :=
        decide_eq_true_eq.mpr hside.disj
      have hkeysDB : decide (∀ n, n ∈ D.map Prod.fst →
          n ∈ questionNames r) = true :=
        decide_eq_true_eq.mpr hside.keysD
      have hkeysHB : decide (∀ n, n ∈ H → n ∈ questionNames r) = true :=
        decide_eq_true_eq.mpr hside.keysH
      have hzipLen : (zipResults Cs Os).length = As.length := by
        have hz := congrArg List.length (zipResults_conclusions hCO)
        simp only [List.length_map] at hz
        exact hz.trans (hside.lenCs.trans hside.lenAs)
      have hpremCs : atomsEquivB canon Cs As = true := by
        rw [← zipResults_conclusions hCO]
        exact hpremB
      simp only [inferSupport, inferSupportRaw]
      rw [hside.rule]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, requireB,
        hside.θNodup, hdomB, hside.prems, hside.concl, hp, hd, hzipLen,
        zipResults_conclusions hCO, hpremCs, hside.qNodup, hside.dNodup,
        hside.hNodup, hcoverB, hdisjB, hkeysDB, hkeysHB, hstrictB,
        hknownB, hassurB, zipResults_obligations hCO,
        zipResults_obligations hDCO]

end Lara.Check
