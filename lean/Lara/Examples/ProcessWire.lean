import Lara.Process.Run
import Lara.Examples.ProcessARA

/-!
Fixtures: the universe carrier on the decoded ARA records of
`Lara.Examples.ProcessARA`.

Each problem pairs an extracted record with a declared universe. The committed
wire fixtures in `fixtures/process/run/` spell the same records; these theorems
are the kernel-checked counterparts of their goldens, and each pins the whole
`Answer` (verdict, completion count and witnesses) for both golden queries,
`precommitted` and `predictable`.

* `omitted_read_universe`: with an unrecorded earlier read declared possible,
  both queries are `unknown` over 10 completions, and each answer names the
  committed-first history as holding and the early-read history as failing.
* `admitted_coverage_universe`, `declared_coverage_universe`: admitted complete
  read coverage makes both `certainTrue` over 2 completions; the same
  attestation as an author declaration is not admitted and leaves the answers
  exactly those of `omitted_read_universe`.
* `contradictory_universe`: contradictory ordering gives `inconsistent` with no
  completions on the ARA fixture, with the same declared unrecorded read.
* `empty_universe_certain`: the same record with an empty universe is
  `certainTrue` over 2 completions, because an empty universe asserts nothing
  unrecorded happened. The universe is an assumption, and
  `certain_antitone_universe` says enlarging it can only lose certainty, as it
  does here.
-/

namespace Lara.Examples.ProcessWire

open Lara.Process
open Lara.Process.Universe
open Lara.Examples.ProcessOrder
open Lara.Examples.ProcessARA

def precommittedQuery : Query := .atom (.runPrecommitted run0)
def predictableQuery : Query := .atom .predictable

/-- The `unknown` answer the goldens record with the early read declared
possible: 10 completions, witnessed both ways. -/
def unknownAnswer : Answer :=
  { verdict := .unknown, count := 10, holds := some [commit, read, run]
    fails := some [earlyRead, commit, read, run] }
def certainAnswer : Answer := { verdict := .certainTrue, count := 2, holds := none, fails := none }
def inconsistentAnswer : Answer :=
  { verdict := .inconsistent, count := 0, holds := none, fails := none }

def omitted : Problem := ⟨extract admits withoutCoverage, [earlyRead]⟩
def logged : Problem := ⟨extract admits withLogCoverage, [earlyRead]⟩
def declared : Problem := ⟨extract admits withDeclaredCoverage, [earlyRead]⟩
def contradictory : Problem := ⟨extract admits contradictorySource, [earlyRead]⟩
def nothingUnrecorded : Problem := ⟨extract admits withoutCoverage, []⟩

theorem omitted_read_universe :
    answer omitted precommittedQuery = unknownAnswer ∧
      answer omitted predictableQuery = unknownAnswer := by
  decide

theorem admitted_coverage_universe :
    answer logged precommittedQuery = certainAnswer ∧
      answer logged predictableQuery = certainAnswer := by
  decide

theorem declared_coverage_universe :
    answer declared precommittedQuery = answer omitted precommittedQuery ∧
      answer declared predictableQuery = answer omitted predictableQuery := by
  decide

theorem contradictory_universe :
    answer contradictory precommittedQuery = inconsistentAnswer ∧
      answer contradictory predictableQuery = inconsistentAnswer := by
  decide

theorem empty_universe_certain :
    answer nothingUnrecorded precommittedQuery = certainAnswer ∧
      answer nothingUnrecorded predictableQuery = certainAnswer ∧
      (answer omitted precommittedQuery).verdict = .unknown := by
  decide

end Lara.Examples.ProcessWire
