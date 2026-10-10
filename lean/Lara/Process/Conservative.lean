import Lara.Process.Coverage
import Lara.BHL.LaraBridge

/-!
Conservativity over the BHL baseline.

The new omission models extend `Lara.BHL.HistoryCoverage` without changing it.
`RecordCoverage.ofHistoryCoverage` reads its only constructor `completeModeled`
as `complete` coverage of a stated scope. `coverage_complete_conservative`
admits that coverage for a bridge history with a process trace: when reports
expose only in-scope events and the artifact warrant reads only in-scope
events, a realized record's verdict is exactly `ArtifactWarrant` at the
generating history. `realized_conservative` states the same agreement for any
record that determines the warrant. Completeness of a test ledger alone does
not discharge the `reads` hypothesis: data accesses and other warrant inputs
must lie in the scope too. Profile checks beyond `ArtifactWarrant` are a
separate obligation.
-/

namespace Lara.Process

open Lara.BHL Lara.Support

/-- The BHL baseline's coverage read as a scoped record coverage. -/
def RecordCoverage.ofHistoryCoverage {Policy : Type} (scope : CoverageScope) :
    HistoryCoverage → RecordCoverage Policy
  | .completeModeled => .complete scope

theorem RecordCoverage.ofHistoryCoverage_complete {Policy : Type} (scope : CoverageScope)
    (c : HistoryCoverage) :
    (RecordCoverage.ofHistoryCoverage (Policy := Policy) scope c) = .complete scope := by
  cases c; rfl

/-- A complete modeled bridge history: an artifact binding with an accepted run
of its exact source. -/
structure BridgeHistory {canon : String → String} (reg : BackendRegistry canon) where
  binding : ArtifactBinding
  run : Update.AcceptedRun reg binding.source

/-- The BHL artifact warrant at a bridge history. -/
def BridgeHistory.warrant {canon : String → String} {reg : BackendRegistry canon}
    (x : BridgeHistory reg) : Prop :=
  ArtifactWarrant x.binding x.run

/-- The complete observation: a record that is the bridge history itself. -/
def completeObservation {canon : String → String} (reg : BackendRegistry canon) :
    RecordSemantics (BridgeHistory reg) (BridgeHistory reg) :=
  ⟨fun r x => x = r⟩

variable {canon : String → String} {reg : BackendRegistry canon}

/-- On any realized record that determines the queried warrant, the base verdict
agrees with `ArtifactWarrant` at the generating history. -/
theorem realized_conservative {R : Type} (S : RecordSemantics (BridgeHistory reg) R)
    {r : R} {x₀ : BridgeHistory reg} (realized : S.compat r x₀)
    (determines : ∀ x, S.compat r x → (x.warrant ↔ x₀.warrant)) :
    (S.verdictOf r BridgeHistory.warrant = .certainTrue ↔ ArtifactWarrant x₀.binding x₀.run) ∧
      (S.verdictOf r BridgeHistory.warrant = .certainFalse ↔
        ¬ ArtifactWarrant x₀.binding x₀.run) :=
  verdict_of_generator realized determines

/-- The complete observation determines every warrant input, so its verdict is
exactly the BHL artifact warrant. -/
theorem completeObservation_conservative (x₀ : BridgeHistory reg) :
    ((completeObservation reg).verdictOf x₀ BridgeHistory.warrant = .certainTrue ↔
        ArtifactWarrant x₀.binding x₀.run) ∧
      ((completeObservation reg).verdictOf x₀ BridgeHistory.warrant = .certainFalse ↔
        ¬ ArtifactWarrant x₀.binding x₀.run) :=
  realized_conservative (completeObservation reg) rfl
    (fun x hx => by cases hx; exact Iff.rfl)

/-- Conservativity over the BHL baseline. Give bridge histories process traces
and let a reporting choice expose only in-scope events. Admit the generating
binding's own `HistoryCoverage`, read as `RecordCoverage.complete scope`. If the
artifact warrant reads only in-scope events, the verdict of a realized record is
exactly `ArtifactWarrant` at the generating history. A complete test scope alone
does not discharge `reads` for a warrant that also depends on data accesses. -/
theorem coverage_complete_conservative {Rho Policy : Type}
    (policy : Policy → ProcessHistory → List Stamped → Prop)
    (trace : BridgeHistory reg → ProcessHistory)
    (exposed : BridgeHistory reg → Rho → List Stamped)
    (S : ProcessModel (BridgeHistory reg) Rho (List Stamped)) (scope : CoverageScope)
    (report : ∀ h rho, S.Report h rho = exposed h rho)
    (inScope : ∀ h rho, S.Valid h → ∀ e ∈ exposed h rho, e ∈ scope.events (trace h))
    (reads : ∀ x y : BridgeHistory reg,
      (∀ e, e ∈ scope.events (trace x) ↔ e ∈ scope.events (trace y)) → (x.warrant ↔ y.warrant))
    {r : List Stamped} {x₀ : BridgeHistory reg × Rho}
    (realized : Compatible S ((RecordCoverage.ofHistoryCoverage scope x₀.1.binding.coverage).assumptions
      policy trace exposed) r x₀) :
    (verdictOf (Compatible S ((RecordCoverage.ofHistoryCoverage scope x₀.1.binding.coverage).assumptions
        policy trace exposed) r) (fun x => x.1.warrant) = .certainTrue ↔
        ArtifactWarrant x₀.1.binding x₀.1.run) ∧
      (verdictOf (Compatible S ((RecordCoverage.ofHistoryCoverage scope x₀.1.binding.coverage).assumptions
        policy trace exposed) r) (fun x => x.1.warrant) = .certainFalse ↔
        ¬ ArtifactWarrant x₀.1.binding x₀.1.run) := by
  rw [RecordCoverage.ofHistoryCoverage_complete] at realized ⊢
  exact complete_coverage_determines policy trace exposed scope report inScope
    (fun x y same => reads x.1 y.1 same) realized

end Lara.Process
