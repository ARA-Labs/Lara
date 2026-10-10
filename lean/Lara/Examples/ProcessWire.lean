import Lara.Process.Run
import Lara.Examples.ProcessARA

/-!
Fixtures: the universe carrier on the decoded ARA records of
`Lara.Examples.ProcessARA`.

Each problem pairs an extracted record with a declared universe. The committed
wire fixtures in `fixtures/process/run/` spell the same records; these theorems
are the kernel-checked counterparts of their goldens.

* `omitted_read_universe`: with an unrecorded earlier read declared possible,
  precommitment is `unknown`, and the answer names the committed-first history
  as holding and the early-read history as failing.
* `admitted_coverage_universe`, `declared_coverage_universe`: admitted complete
  read coverage makes it `certainTrue`; the same attestation as an author
  declaration is not admitted and leaves it `unknown`.
* `contradictory_universe`: contradictory ordering gives `inconsistent` over any
  universe.
* `empty_universe_certain`: the same record with an empty universe is
  `certainTrue`, because an empty universe asserts nothing unrecorded happened.
  The universe is an assumption, and `certain_antitone_universe` says enlarging
  it can only lose certainty, as it does here.
-/

namespace Lara.Examples.ProcessWire

open Lara.Process
open Lara.Process.Universe
open Lara.Examples.ProcessOrder
open Lara.Examples.ProcessARA

def precommittedQuery : Query := .atom (.runPrecommitted run0)

def omitted : Problem := ⟨extract admits withoutCoverage, [earlyRead]⟩
def logged : Problem := ⟨extract admits withLogCoverage, [earlyRead]⟩
def declared : Problem := ⟨extract admits withDeclaredCoverage, [earlyRead]⟩
def contradictory : Problem := ⟨extract admits contradictorySource, [earlyRead]⟩
def nothingUnrecorded : Problem := ⟨extract admits withoutCoverage, []⟩

theorem omitted_read_universe :
    answer omitted precommittedQuery =
      { verdict := .unknown, count := 10, holds := some [commit, read, run]
        fails := some [earlyRead, commit, read, run] } := by
  decide

theorem admitted_coverage_universe :
    (answer logged precommittedQuery).verdict = .certainTrue ∧
      (answer logged precommittedQuery).count = 2 := by
  decide

theorem declared_coverage_universe : (answer declared precommittedQuery).verdict = .unknown := by
  decide

theorem contradictory_universe :
    (answer contradictory precommittedQuery).verdict = .inconsistent := by
  decide

theorem empty_universe_certain :
    (answer nothingUnrecorded precommittedQuery).verdict = .certainTrue ∧
      (answer omitted precommittedQuery).verdict = .unknown := by
  decide

end Lara.Examples.ProcessWire
