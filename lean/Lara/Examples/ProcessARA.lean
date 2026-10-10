import Lara.Process.Bridge
import Lara.Examples.ProcessOrder

/-!
Fixtures: decoded ARA records with source references.

Each fixture is an `AraSource` whose entries cite the ARA file and entry they
came from. The plan commit, the evaluation read and the run reuse the events of
`Lara.Examples.ProcessOrder`, and the candidate complete histories are its
`Candidate` traces.

* `omitted_read_ara`: ordering evidence alone leaves precommitment `unknown`.
* `admitted_coverage_ara`: an instrumented-log attestation of complete
  evaluation-read coverage, admitted by the reader, makes it `certainTrue`.
* `declared_coverage_not_admitted`: the same attestation on the basis of an
  author declaration is not admitted, so the verdict stays `unknown`.
* `generating_history_compatible`: the committed-first history satisfies the
  source relation, so extraction keeps it compatible and every certain verdict
  holds there.
* `failed_trial_preserved`: a failed sibling trial survives extraction.
* `contradictory_ara_inconsistent`: contradictory ordering entries yield
  `inconsistent`.
-/

namespace Lara.Examples.ProcessARA

open Lara.Process
open Lara.Examples.ProcessOrder

def ref (file entry : String) : SourceRef := ⟨file, entry, none⟩

/-- The reported events and the stated order. -/
def baseEntries : List (AraEntry Empty) :=
  [.event commit (ref "experiments/plan.md" "commit-v0"),
   .event read ⟨"logs/access.md", "read-test", some (12, 18)⟩,
   .event run (ref "experiments/run0.md" "run0"),
   .ordering commit.id read.id ⟨"logs/access.md", "after-commit", some (20, 21)⟩,
   .submission ⟨0⟩ ⟨0⟩]

/-- An attestation of complete evaluation-read coverage. -/
def accessAttestation (basis : AdmissionBasis) : AraEntry Empty :=
  .coverage ⟨.complete accessScope, ref "logs/access.md" "coverage", basis⟩

def withoutCoverage : AraSource Empty := ⟨baseEntries, 10⟩
def withLogCoverage : AraSource Empty := ⟨baseEntries ++ [accessAttestation .instrumentedLog], 10⟩
def withDeclaredCoverage : AraSource Empty :=
  ⟨baseEntries ++ [accessAttestation .authorDeclaration], 10⟩

/-- The reader admits instrumented logs and signed attestations, not author
declarations. -/
def admits : AdmissionBasis → Bool
  | .authorDeclaration => false
  | _ => true

def decodedCompat (src : AraSource Empty) (x : Candidate) : Prop :=
  (extract admits src).Compatible noPolicy x.trace

instance (src : AraSource Empty) : DecidablePred (decodedCompat src) :=
  fun _ => inferInstanceAs (Decidable (DecodedRecord.Compatible _ _ _))

theorem omitted_read_ara : verdict (decodedCompat withoutCoverage) precommitted = .unknown := by
  decide

/-- The same recorded plan and evaluation are compatible both with the history
that only reads after the commit and with one that also read the evaluation data
earlier: the earlier read is simply unrecorded. -/
theorem omitted_read_compatible :
    decodedCompat withoutCoverage .committedFirst ∧ decodedCompat withoutCoverage .earlierRead ∧
      precommitted .committedFirst ∧ ¬ precommitted .earlierRead := by
  decide

theorem admitted_coverage_ara :
    verdict (decodedCompat withLogCoverage) precommitted = .certainTrue := by
  decide

theorem declared_coverage_not_admitted :
    verdict (decodedCompat withDeclaredCoverage) precommitted = .unknown := by
  decide

/-- The committed-first history is faithfully described by the logged source, so
it stays compatible with the extraction, and the certain precommitment verdict
holds there. -/
theorem generating_history_compatible :
    SourceRel noPolicy admits withLogCoverage Candidate.committedFirst.trace ∧
      (extract admits withLogCoverage).Compatible noPolicy Candidate.committedFirst.trace ∧
      precommitted .committedFirst := by
  have rel : SourceRel noPolicy admits withLogCoverage Candidate.committedFirst.trace := by
    refine ⟨by decide, ?_, ?_, ?_⟩
    · intro e s mem; simp [withLogCoverage, baseEntries, accessAttestation] at mem
      rcases mem with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
    · intro a b s mem; simp [withLogCoverage, baseEntries, accessAttestation] at mem
      obtain ⟨rfl, rfl, _⟩ := mem; decide
    · intro c mem _
      simp [withLogCoverage, baseEntries, accessAttestation] at mem
      subst mem; decide
  exact ⟨rel, extraction_preserves_compatibility noPolicy admits withLogCoverage rel, by decide⟩

/-- A failed sibling run lowers to no attack edge but survives extraction. -/
def withSiblingSource : AraSource Empty :=
  ⟨baseEntries ++ [.event siblingRun (ref "exploration/branches.md" "failed-sibling"),
    .event failure (ref "exploration/branches.md" "failed-sibling-result")], 20⟩

theorem failed_trial_preserved :
    siblingRun ∈ (extract admits withSiblingSource).toOrderRecord.events ∧
      failure ∈ (extract admits withSiblingSource).toOrderRecord.events := by
  decide

/-- Contradictory ordering entries. -/
def contradictorySource : AraSource Empty :=
  ⟨baseEntries ++ [.ordering read.id commit.id (ref "logs/access.md" "before-commit")], 10⟩

theorem contradictory_ara_inconsistent :
    verdict (decodedCompat contradictorySource) precommitted = .inconsistent := by
  decide

/-- The submissions survive extraction with the record. -/
theorem submission_extracted :
    (extract admits withLogCoverage).submitted = [(⟨0⟩, ⟨0⟩)] := by
  decide

/-- The logged source with its entries in another file order. -/
def reorderedSource : AraSource Empty := ⟨withLogCoverage.entries.reverse, 10⟩

/-- File order is not evidence: the reordered source decodes to an equivalent
record, so every verdict on it is the same. -/
theorem reordered_equivalent (φ : ProcessHistory → Prop) :
    verdictOf ((extract admits reorderedSource).Compatible noPolicy) φ =
      verdictOf ((extract admits withLogCoverage).Compatible noPolicy) φ := by
  apply verdict_invariant
  have order : (extract admits reorderedSource).order = (extract admits withLogCoverage).order := by
    decide
  have coverage :
      (extract admits reorderedSource).coverage = (extract admits withLogCoverage).coverage := by
    decide
  apply perm_equivalent (d := extract admits reorderedSource) (d' := extract admits withLogCoverage)
    noPolicy (by decide) (fun c => by rw [order]) (fun c => by rw [coverage]) rfl
  intro c h r r' perm
  exact RecordCoverage.allowed_perm noPolicy (fun p => p.elim) c h perm

end Lara.Examples.ProcessARA
