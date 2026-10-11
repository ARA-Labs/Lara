import Lara.Process.Wire

/-!
The `process-run` evaluator: a decoded `process-input 1` document to a
`process-result 1` or a refusal.

Evaluation fails closed. A document whose events exceed its limit or the
checker's ceiling, whose completions exceed theirs, or that asks for an audit,
is refused and gets no verdict at all (`run_eventLimit`, `run_completionLimit`,
`run_audit`). Audits are part of the frozen grammar, but executing one needs
each completion's argumentation framework from a checked Lara source; until that
runtime exists, an audit of a submitted witness is refused as `unsupported`, and
an audit of a witness the record does not submit is `malformed`. An accepted
document's answers are exactly `Universe.answer` of its problem
(`run_answers`), so every theorem of `Lara.Process.Universe` and
`Lara.Process.Rename` applies to what the runner prints.
-/

namespace Lara.Process.Wire

open Lara.Process
open Lara.Process.Universe
open Lara.Driver (Sx)

/-- The checker's ceilings, which no document can raise. The reference
enumerator is exponential in the event count; a faster generator may raise
`maxProcessEvents` once it is proved equal to the reference one. -/
def maxProcessEvents : Nat := 8
def maxProcessCompletions : Nat := 10000

namespace Document

def admitsBasis (d : Document) (b : AdmissionBasis) : Bool := d.admits.contains b

/-- The decoded problem: the record extracted under the reader's admitted bases,
and the declared universe. -/
def problem (d : Document) : Problem := ⟨extract d.admitsBasis d.source, d.unrecorded⟩

/-- Coverage attestations whose basis the reader does not admit. They are
reported, never applied. -/
def unadmitted (d : Document) : List (CoverageAssertion Empty) :=
  (d.source.entries.filterMap AraEntry.coverage?).filter fun c => !d.admitsBasis c.basis

def eventLimit (d : Document) : Nat := min d.limits.events maxProcessEvents
def completionLimit (d : Document) : Nat := min d.limits.completions maxProcessCompletions

end Document

/-- The distinct events a completion may contain. -/
def _root_.Lara.Process.Universe.Problem.eventCount (p : Problem) : Nat := (p.base ++ p.unrecorded).dedup.length

/-- Why a query cannot run in version 1, if it cannot. -/
def auditFault (submitted : List (ClaimId × WitnessId)) : QuerySpec → Option Error
  | .verdict .. => none
  | .audit name c w _ =>
    if (c, w) ∈ submitted then
      some ⟨.unsupported, s!"audit {name} needs the checked-source runtime"⟩
    else some ⟨.malformed, s!"audit {name} names a witness the record does not submit"⟩

def verdictQuery (cs : List ProcessHistory) : QuerySpec → Option (String × Answer)
  | .verdict name q => some (name, answerOf cs q)
  | .audit .. => none

structure Result where
  problem : Problem
  unadmitted : List (CoverageAssertion Empty)
  limits : Limits
  answers : List (String × Answer)
  deriving DecidableEq, Repr

def run (d : Document) : Except Error Result :=
  match d.queries.findSome? (auditFault d.problem.record.submitted) with
  | some e => .error e
  | none =>
    if d.eventLimit < d.problem.eventCount then
      .error ⟨.limitExceeded,
        s!"{d.problem.eventCount} events exceed the event limit {d.eventLimit}"⟩
    else
      if d.completionLimit < d.problem.completions.length then
        .error ⟨.limitExceeded, s!"{d.problem.completions.length} completions exceed the completion limit {d.completionLimit}"⟩
      else
        .ok ⟨d.problem, d.unadmitted, d.limits,
          d.queries.filterMap (verdictQuery d.problem.completions)⟩

/-- An accepted document's answers are the universe answers of its problem, one
per query in order. -/
theorem run_answers {d : Document} {r : Result} (h : run d = .ok r) :
    r.problem = d.problem ∧
      r.answers = d.queries.filterMap fun
        | .verdict name q => some (name, answer d.problem q)
        | .audit .. => none := by
  unfold run at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h
        exact ⟨rfl, rfl⟩

/-- An accepted document is within both limits. -/
theorem run_within_limits {d : Document} {r : Result} (h : run d = .ok r) :
    d.problem.eventCount ≤ d.eventLimit ∧ d.problem.completions.length ≤ d.completionLimit := by
  unfold run at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · exact ⟨Nat.le_of_not_lt ‹_›, Nat.le_of_not_lt ‹_›⟩

/-- Too many events: no verdict at all. -/
theorem run_eventLimit {d : Document} (over : d.eventLimit < d.problem.eventCount) (r : Result) :
    run d ≠ .ok r := fun h => absurd (run_within_limits h).1 (Nat.not_le_of_lt over)

/-- Too many completions: no verdict at all. -/
theorem run_completionLimit {d : Document} (over : d.completionLimit < d.problem.completions.length)
    (r : Result) : run d ≠ .ok r := fun h => absurd (run_within_limits h).2 (Nat.not_le_of_lt over)

/-- A document with an audit gets no verdict in version 1. -/
theorem run_audit {d : Document} {name : String} {c : ClaimId} {w : WitnessId} {p : ProfileSpec}
    (mem : QuerySpec.audit name c w p ∈ d.queries) (r : Result) : run d ≠ .ok r := by
  intro h
  unfold run at h
  split at h
  · cases h
  · rename_i none
    rw [List.findSome?_eq_none_iff] at none
    have := none _ mem
    simp only [auditFault] at this
    split at this <;> cases this

/-! ### Result and refusal envelopes -/

def encodeHistory (n : Names) (h : ProcessHistory) : Sx :=
  tagged .history (h.map fun e => encodeIdx n.event e.id.index)

def encodeAnswer (n : Names) (a : String × Answer) : Sx :=
  tagged .answer ([.atom a.1, .atom (Verdict.spelling.text a.2.verdict),
      encodeField .completions a.2.count] ++
    (a.2.holds.map fun h => tagged .holds [encodeHistory n h]).toList ++
    (a.2.fails.map fun h => tagged .fails [encodeHistory n h]).toList)

def encodeAssertion (n : Names) (c : CoverageAssertion Empty) : Sx := encodeEntry n (.coverage c)

/-- `(process-result 1 (assumptions ...) (answers ...))`. Every verdict is
conditional on the printed universe, admitted coverage and limits. -/
def encodeResult (n : Names) (r : Result) : Sx :=
  tagged .processResult [.atom version,
    tagged .assumptions [encodeUniverse n r.problem.unrecorded,
      tagged .admitted (r.problem.record.coverage.map (encodeAssertion n)),
      tagged .unadmitted (r.unadmitted.map (encodeAssertion n)),
      encodeLimits r.limits],
    tagged .answers (r.answers.map (encodeAnswer n))]

/-- `(process-error 1 TAG DETAIL)`. -/
def encodeError (e : Error) : Sx :=
  tagged .processError [.atom version, .atom (ErrorTag.spelling.text e.tag), .atom e.detail]

/-- Text to document: a reader failure is `syntax`, everything else is the
structured decoder's verdict. -/
def parse (text : String) : Except Error Document :=
  match Lara.Driver.parseWire text with
  | .error e => .error ⟨.syntax, e⟩
  | .ok sx => decodeDocument sx

/-- The whole pipeline on text: the printed envelope and the exit code. -/
def process (text : String) : Sx × UInt32 :=
  match parse text with
  | .error e => (encodeError e, e.exitCode)
  | .ok d =>
    match run d with
    | .error e => (encodeError e, e.exitCode)
    | .ok r => (encodeResult d.names r, 0)

end Lara.Process.Wire
