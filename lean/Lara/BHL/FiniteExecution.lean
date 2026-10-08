import Lara.Examples.BHLBinaryRuns

/-!
Executable binary small steps and bounded exploration of the existing typed
source language. Fuel counts reference small steps, including silent guards.
Parallel choices are enumerated recursively, not selected by a uniform Boolean.
This module makes no unbounded validity or termination claim.
-/

namespace Lara.BHL.FiniteExecution

open Lara.BHL
open Lara.Examples.BHLExecution (Source Command IntExpr Guard Snapshot Event Reifies
  eventWorld eventsWorld)
open Lara.Examples.BHLBinaryModel (interpretation context)
open Lara.Examples.BHLSoundnessScience (Prior)

/-- Actual calibrated effects; the old Dirac command evaluator is not used. -/
def evalCommand (state : Snapshot) : Command → Option Snapshot
  | .skip => some state
  | .assign target expr => (expr.eval state).map fun value =>
      { state with integers := Function.update state.integers target.id (some value) }
  | .alias target source => some
      { state with datasets := Function.update state.datasets target (state.datasets source) }
  | .test target data name => some (Lara.Examples.BHLBinaryRuns.runTest state target data name)
  | .pvalue target data _ => some (Lara.Examples.BHLBinaryRuns.runPvalue state target data)

def commandDelta (state : Snapshot) : Command → History Bool
  | .test _ data name => {(state.datasets data, name)}
  | _ => 0

abbrev Next := Option Source × Event

def liftLeft (combine : Source → Source → Source) (right : Source) (out : Next) : Next :=
  (some (match out.1 with | none => right | some left => combine left right), out.2)

def liftRight (left : Source) (out : Next) : Next :=
  (some (match out.1 with | none => left | some right => .par left right), out.2)

/-- Every parallel node independently enumerates its left and right steps. -/
def nextAll : Source → Snapshot → List Next
  | .command command, state =>
      match evalCommand state command with
      | none => []
      | some after => [(none, ⟨some command, after⟩)]
  | .seq left right, state => (nextAll left state).map (liftLeft .seq right)
  | .ite guard left right, state =>
      match guard.eval state with
      | none => []
      | some value => [(some (if value then left else right), ⟨none, state⟩)]
  | .loop guard body, state =>
      match guard.eval state with
      | none => []
      | some value => [(if value then some (.seq body (.loop guard body)) else none,
          ⟨none, state⟩)]
  | .par left right, state =>
      (nextAll left state).map (liftLeft .par right) ++
      (nextAll right state).map (liftRight left)

inductive Failure where
  | malformedSource
  | undefinedStep
  | scheduleChoice (index : Nat)
  deriving DecidableEq, Repr

inductive Status where
  | completed
  | incomplete
  | failed (reason : Failure)
  deriving DecidableEq, Repr

structure Outcome where
  status : Status
  residual : Option Source
  state : Snapshot
  events : List Event

def Outcome.prepend (event : Event) (out : Outcome) : Outcome :=
  { out with events := event :: out.events }

/-- Terminal configurations succeed even at zero fuel. Nonterminal zero fuel
is incomplete, not failure, and cannot establish universal validity. -/
def explore : Nat → Option Source → Snapshot → List Outcome
  | _, none, state => [⟨.completed, none, state, []⟩]
  | 0, some source, state => [⟨.incomplete, some source, state, []⟩]
  | fuel + 1, some source, state =>
      match nextAll source state with
      | [] => [⟨.failed .undefinedStep, some source, state, []⟩]
      | nexts => nexts.flatMap fun out =>
          (explore fuel out.1 out.2.state).map (Outcome.prepend out.2)

/-- Closed malformed-source reporting precedes bounded operational exploration. -/
def exhaustiveRun (fuel : Nat) (source : Source) (state : Snapshot) : List Outcome :=
  if source.quote.wellFormedCheck then explore fuel (some source) state
  else [⟨.failed .malformedSource, some source, state, []⟩]

/-- A schedule gives an index into the full recursively enumerated next-step
list, so it can replay mixed nested-parallel choices. An exhausted schedule is
incomplete; a nonexistent choice is a distinct closed failure. -/
def replay : List Nat → Option Source → Snapshot → Outcome
  | _, none, state => ⟨.completed, none, state, []⟩
  | [], some source, state => ⟨.incomplete, some source, state, []⟩
  | choice :: rest, some source, state =>
      match nextAll source state with
      | [] => ⟨.failed .undefinedStep, some source, state, []⟩
      | nexts => match nexts[choice]? with
        | none => ⟨.failed (.scheduleChoice choice), some source, state, []⟩
        | some out => (replay rest out.1 out.2.state).prepend out.2

def scheduledRun (schedule : List Nat) (source : Source) (state : Snapshot) : Outcome :=
  if source.quote.wellFormedCheck then replay schedule (some source) state
  else ⟨.failed .malformedSource, some source, state, []⟩

noncomputable section

 theorem integer_correspondence (state : Snapshot) (expr : IntExpr) :
    evalProgramExpr interpretation state.visible expr.quote = expr.eval state := by
  induction expr with
  | literal value => rfl
  | read target => rfl
  | add a b ha hb => simp [IntExpr.quote, evalProgramExpr, IntExpr.eval, ha, hb]

 theorem guard_correspondence (state : Snapshot) (guard : Guard) :
    evalProgramExpr interpretation state.visible guard.quote = guard.eval state := by
  cases guard with
  | literal value => rfl
  | less a b => simp [Guard.quote, Guard.eval, evalProgramExpr, integer_correspondence]

private theorem integer_write (state : Snapshot) (target : Variable .integer .observable)
    (value : Int) :
    (VisibleWrite.value target value).apply state.visible =
      ({state with integers := Function.update state.integers target.id (some value)} : Snapshot).visible := by
  apply congrArg₂ VisibleState.mk
  · funext sort name
    by_cases sameName : name = target.id
    · rw [sameName]
      cases sort <;> simp [Snapshot.visible, Snapshot.memory,
        Memory.observable, Memory.update, Memory.assemble, Function.update]
    · cases sort <;> simp [Snapshot.visible, Snapshot.memory,
        Memory.observable, Memory.update, Memory.assemble, Function.update,
        sameName, Ne.symm sameName]
  · rfl

/-- Exact primitive-effect equality, not just agreement of reports or counts. -/
 theorem command_effect (state : Snapshot) (command : Command) :
    primitiveEffect interpretation command.quote state.visible =
      (evalCommand state command).map fun after => (after.visible, commandDelta state command) := by
  cases command with
  | skip => rfl
  | assign target expr =>
      cases h : expr.eval state with
      | none => simp [evalCommand, primitiveEffect, evalPrimitive, Command.quote,
          integer_correspondence, h]
      | some value => simp [evalCommand, primitiveEffect, evalPrimitive, Command.quote,
          integer_correspondence, h, integer_write, commandDelta]
  | «alias» target source => rfl
  | test target data name => exact Lara.Examples.BHLBinaryRuns.test_effect state target data name
  | pvalue target data name => exact Lara.Examples.BHLBinaryRuns.pvalue_effect state target data name

 theorem command_ledger (state after : Snapshot) (command : Command)
    (computed : evalCommand state command = some after) :
    after.ledger = state.ledger + commandDelta state command := by
  cases command with
  | assign target expr =>
      cases h : expr.eval state with
      | none => simp [evalCommand, h] at computed
      | some value =>
          simp [evalCommand, h] at computed
          subst after
          simp [commandDelta]
  | skip =>
      simp [evalCommand] at computed
      subst after
      simp [commandDelta]
  | «alias» target source =>
      simp [evalCommand] at computed
      subst after
      simp [commandDelta]
  | test target data name =>
      simp [evalCommand] at computed
      subst after
      rfl
  | pvalue target data name =>
      simp [evalCommand] at computed
      subst after
      simp [commandDelta, Lara.Examples.BHLBinaryRuns.runPvalue]

private theorem command_event_eq (world : World Bool Primitive) (state after : Snapshot)
    (command : Command) (represented : Reifies world state)
    (computed : evalCommand state command = some after) :
    eventWorld world ⟨some command, after⟩ = world.extend
      (commandState world.current command.quote after.visible (commandDelta state command)) := by
  have ledger := command_ledger state after command computed
  simp [eventWorld, commandState, Snapshot.visible, ledger, represented.2]

private theorem command_step (prior : Prior) (world : World Bool Primitive)
    (state after : Snapshot) (command : Command) (represented : Reifies world state)
    (computed : evalCommand state command = some after) :
    Step (context prior) (some (.command command.quote)) world none
      (eventWorld world ⟨some command, after⟩) ∧
      Reifies (eventWorld world ⟨some command, after⟩) after := by
  have enabled : primitiveEffect (context prior).interpretation command.quote world.current.visible =
      some (after.visible, commandDelta state command) := by
    change primitiveEffect interpretation _ _ = _
    rw [represented.1, command_effect, computed]
    rfl
  constructor
  · rw [command_event_eq world state after command represented computed]
    exact .command enabled
  · simp [Reifies, eventWorld, State.visible, Snapshot.visible]

/-- Soundness of every computed next step, including all nested parallel paths. -/
 theorem nextAll_correspondence (prior : Prior) (source : Source) (state : Snapshot)
    (out : Next) (world : World Bool Primitive) (represented : Reifies world state)
    (computed : out ∈ nextAll source state) :
    Step (context prior) (some source.quote) world (out.1.map Source.quote)
      (eventWorld world out.2) ∧ Reifies (eventWorld world out.2) out.2.state := by
  induction source generalizing state out world with
  | command command =>
      cases h : evalCommand state command with
      | none => simp [nextAll, h] at computed
      | some after =>
          simp [nextAll, h] at computed
          subst out
          exact command_step prior world state after command represented h
  | seq a b ihA ihB =>
      obtain ⟨child, member, rfl⟩ := List.mem_map.mp computed
      obtain ⟨step, repr⟩ := ihA state child world represented member
      refine ⟨?_, repr⟩
      cases h : child.1 with
      | none => simpa [liftLeft, Source.quote, h] using Step.seqFinish (by simpa [h] using step)
      | some next => simpa [liftLeft, Source.quote, h] using Step.seqContinue (by simpa [h] using step)
  | ite guard a b ihA ihB =>
      cases h : guard.eval state with
      | none => simp [nextAll, h] at computed
      | some value =>
          simp [nextAll, h] at computed
          subst out
          have enabled : evalProgramExpr (context prior).interpretation world.current.visible guard.quote =
              some value := by
            change evalProgramExpr interpretation _ _ = _
            rw [represented.1, guard_correspondence, h]
          cases value
          · exact ⟨.ifFalse enabled, represented⟩
          · exact ⟨.ifTrue enabled, represented⟩
  | loop guard body ih =>
      cases h : guard.eval state with
      | none => simp [nextAll, h] at computed
      | some value =>
          simp [nextAll, h] at computed
          subst out
          have enabled : evalProgramExpr (context prior).interpretation world.current.visible guard.quote =
              some value := by
            change evalProgramExpr interpretation _ _ = _
            rw [represented.1, guard_correspondence, h]
          cases value
          · exact ⟨.loopFalse enabled, represented⟩
          · exact ⟨.loopTrue enabled, represented⟩
  | par a b ihA ihB =>
      rcases List.mem_append.mp computed with left | right
      · obtain ⟨child, member, rfl⟩ := List.mem_map.mp left
        obtain ⟨step, repr⟩ := ihA state child world represented member
        refine ⟨?_, repr⟩
        cases h : child.1 with
        | none => simpa [liftLeft, Source.quote, h] using Step.parLeftFinish (by simpa [h] using step)
        | some next => simpa [liftLeft, Source.quote, h] using Step.parLeftContinue (by simpa [h] using step)
      · obtain ⟨child, member, rfl⟩ := List.mem_map.mp right
        obtain ⟨step, repr⟩ := ihB state child world represented member
        refine ⟨?_, repr⟩
        cases h : child.1 with
        | none => simpa [liftRight, Source.quote, h] using Step.parRightFinish (by simpa [h] using step)
        | some next => simpa [liftRight, Source.quote, h] using Step.parRightContinue (by simpa [h] using step)

private theorem command_complete (prior : Prior) (command : Command)
    (state : Snapshot) (world : World Bool Primitive) (target : Option Program)
    (after : World Bool Primitive) (represented : Reifies world state)
    (step : Step (context prior) (some (.command command.quote)) world target after) :
    ∃ out ∈ nextAll (.command command) state,
      out.1.map Source.quote = target ∧ eventWorld world out.2 = after := by
  cases step with
  | command enabled =>
      change primitiveEffect interpretation command.quote world.current.visible = _ at enabled
      rw [represented.1, command_effect] at enabled
      cases h : evalCommand state command with
      | none => simp [h] at enabled
      | some final =>
          simp only [h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at enabled
          rcases enabled with ⟨rfl, rfl⟩
          exact ⟨(none, ⟨some command, final⟩), by simp [nextAll, h], rfl,
            command_event_eq world state final command represented h⟩

/-- Converse coverage is proved against the independent Step relation. No
schedule membership assumption occurs in this theorem. -/
 theorem nextAll_complete (prior : Prior) (source : Source) (state : Snapshot)
    (world : World Bool Primitive) (target : Option Program) (after : World Bool Primitive)
    (represented : Reifies world state)
    (step : Step (context prior) (some source.quote) world target after) :
    ∃ out ∈ nextAll source state,
      out.1.map Source.quote = target ∧ eventWorld world out.2 = after := by
  induction source generalizing state world target after with
  | command command => exact command_complete prior command state world target after represented step
  | seq a b ihA ihB =>
      cases step with
      | seqContinue child =>
          obtain ⟨out, member, residual, final⟩ := ihA state world _ after represented child
          refine ⟨liftLeft .seq b out, List.mem_map.mpr ⟨out, member, rfl⟩, ?_, final⟩
          cases h : out.1 <;> simp [h] at residual
          simpa [liftLeft, Source.quote, h, residual]
      | seqFinish child =>
          obtain ⟨out, member, residual, final⟩ := ihA state world _ after represented child
          refine ⟨liftLeft .seq b out, List.mem_map.mpr ⟨out, member, rfl⟩, ?_, final⟩
          cases h : out.1 <;> simp [h] at residual
          simp [liftLeft, h]
  | ite guard a b ihA ihB =>
      cases step with
      | ifTrue enabled =>
          change evalProgramExpr interpretation world.current.visible guard.quote = some true at enabled
          rw [represented.1, guard_correspondence] at enabled
          exact ⟨(some a, ⟨none, state⟩), by simp [nextAll, enabled], rfl, rfl⟩
      | ifFalse enabled =>
          change evalProgramExpr interpretation world.current.visible guard.quote = some false at enabled
          rw [represented.1, guard_correspondence] at enabled
          exact ⟨(some b, ⟨none, state⟩), by simp [nextAll, enabled], rfl, rfl⟩
  | loop guard body ih =>
      cases step with
      | loopTrue enabled =>
          change evalProgramExpr interpretation world.current.visible guard.quote = some true at enabled
          rw [represented.1, guard_correspondence] at enabled
          exact ⟨(some (.seq body (.loop guard body)), ⟨none, state⟩),
            by simp [nextAll, enabled], rfl, rfl⟩
      | loopFalse enabled =>
          change evalProgramExpr interpretation world.current.visible guard.quote = some false at enabled
          rw [represented.1, guard_correspondence] at enabled
          exact ⟨(none, ⟨none, state⟩), by simp [nextAll, enabled], rfl, rfl⟩
  | par a b ihA ihB =>
      cases step with
      | parLeftContinue child =>
          obtain ⟨out, member, residual, final⟩ := ihA state world _ after represented child
          refine ⟨liftLeft .par b out, List.mem_append_left _ (List.mem_map.mpr ⟨out, member, rfl⟩), ?_, final⟩
          cases h : out.1 <;> simp [h] at residual
          simpa [liftLeft, Source.quote, h, residual]
      | parLeftFinish child =>
          obtain ⟨out, member, residual, final⟩ := ihA state world _ after represented child
          refine ⟨liftLeft .par b out, List.mem_append_left _ (List.mem_map.mpr ⟨out, member, rfl⟩), ?_, final⟩
          cases h : out.1 <;> simp [h] at residual
          simp [liftLeft, h]
      | parRightContinue child =>
          obtain ⟨out, member, residual, final⟩ := ihB state world _ after represented child
          refine ⟨liftRight a out, List.mem_append_right _ (List.mem_map.mpr ⟨out, member, rfl⟩), ?_, final⟩
          cases h : out.1 <;> simp [h] at residual
          simpa [liftRight, Source.quote, h, residual]
      | parRightFinish child =>
          obtain ⟨out, member, residual, final⟩ := ihB state world _ after represented child
          refine ⟨liftRight a out, List.mem_append_right _ (List.mem_map.mpr ⟨out, member, rfl⟩), ?_, final⟩
          cases h : out.1 <;> simp [h] at residual
          simp [liftRight, h]

/-- Empty computed successors means undefined execution, not a missing schedule. -/
 theorem nextAll_empty_iff (prior : Prior) (source : Source) (state : Snapshot)
    (world : World Bool Primitive) (represented : Reifies world state) :
    nextAll source state = [] ↔
      ¬ ∃ target after, Step (context prior) (some source.quote) world target after := by
  constructor
  · intro empty ⟨target, after, step⟩
    obtain ⟨out, member, _, _⟩ := nextAll_complete prior source state world target after represented step
    simp [empty] at member
  · intro absent
    cases h : nextAll source state with
    | nil => rfl
    | cons out rest =>
        have member : out ∈ nextAll source state := by simp [h]
        exact False.elim (absent ⟨_, _, (nextAll_correspondence prior source state out world represented member).1⟩)

/-- Every explored outcome preserves the literal event trace and has an exact
reference prefix witness, even when the search is incomplete or undefined. -/
 theorem explore_correspondence (prior : Prior) (fuel : Nat) (source : Option Source)
    (state : Snapshot) (out : Outcome) (world : World Bool Primitive)
    (represented : Reifies world state) (member : out ∈ explore fuel source state) :
    Steps (context prior) out.events.length (source.map Source.quote) world
      (out.residual.map Source.quote) (eventsWorld world out.events) ∧
      Reifies (eventsWorld world out.events) out.state ∧ out.events.length ≤ fuel ∧
      (out.status = .completed → out.residual = none) := by
  induction fuel generalizing source state out world with
  | zero =>
      cases source <;> simp [explore] at member <;> subst out
      all_goals exact ⟨.refl _ _, represented, by simp, by simp⟩
  | succ fuel ih =>
      cases source with
      | none =>
          simp [explore] at member
          subst out
          exact ⟨.refl _ _, represented, by simp, by simp⟩
      | some source =>
          cases h : nextAll source state with
          | nil =>
              simp [explore, h] at member
              subst out
              exact ⟨.refl _ _, represented, by simp, by simp⟩
          | cons first rest =>
              simp only [explore, h, List.mem_flatMap] at member
              obtain ⟨next, member, tail⟩ := member
              obtain ⟨result, resultMember, rfl⟩ := List.mem_map.mp tail
              have nextMember : next ∈ nextAll source state := by simpa [h] using member
              obtain ⟨step, repr⟩ := nextAll_correspondence prior source state next world represented nextMember
              obtain ⟨steps, finalRepr, bound, terminal⟩ := ih next.1 next.2.state result
                (eventWorld world next.2) repr resultMember
              refine ⟨?_, ?_, ?_, terminal⟩
              · simpa [Outcome.prepend, eventsWorld] using Steps.cons step steps
              · simpa [Outcome.prepend, eventsWorld] using finalRepr
              · simpa [Outcome.prepend] using Nat.succ_le_succ bound

/-- All terminating reference runs of exact length n are present whenever
n ≤ fuel. The hypothesis is independent Steps, not generated schedules. -/
 theorem explore_coverage (prior : Prior) (fuel : Nat) (source : Option Source)
    (state : Snapshot) (world after : World Bool Primitive) (n : Nat)
    (represented : Reifies world state)
    (steps : Steps (context prior) n (source.map Source.quote) world none after)
    (bound : n ≤ fuel) :
    ∃ out ∈ explore fuel source state,
      out.status = .completed ∧ out.residual = none ∧ out.events.length = n ∧
      eventsWorld world out.events = after := by
  induction fuel generalizing source state world after n with
  | zero =>
      have zero : n = 0 := Nat.eq_zero_of_le_zero bound
      subst n
      obtain ⟨terminal, rfl⟩ := Steps.zero_iff.mp steps
      cases source with
      | none => exact ⟨⟨.completed, none, state, []⟩, by simp [explore], rfl, rfl, rfl, rfl⟩
      | some source => simp at terminal
  | succ fuel ih =>
      cases source with
      | none =>
          obtain ⟨rfl, _, rfl⟩ := Steps.terminal_iff.mp steps
          exact ⟨⟨.completed, none, state, []⟩, by simp [explore], rfl, rfl, rfl, rfl⟩
      | some source =>
          cases steps with
          | @cons length _ middle _ _ intermediate _ first rest =>
              obtain ⟨next, member, residual, final⟩ :=
                nextAll_complete prior source state world middle intermediate represented first
              have repr := (nextAll_correspondence prior source state next world represented member).2
              have tailSteps : Steps (context prior) length (next.1.map Source.quote)
                  (eventWorld world next.2) none after := by rw [residual, final]; exact rest
              obtain ⟨out, tailMember, completed, terminal, count, endpoint⟩ :=
                ih next.1 next.2.state (eventWorld world next.2) after length repr tailSteps
                  (Nat.le_of_succ_le_succ bound)
              refine ⟨out.prepend next.2, ?_, completed, terminal, ?_, ?_⟩
              · cases h : nextAll source state with
                | nil => simp [h] at member
                | cons first rest =>
                    simp only [explore, h, List.mem_flatMap]
                    exact ⟨next, by simpa [h] using member, List.mem_map.mpr ⟨out, tailMember, rfl⟩⟩
              · simp [Outcome.prepend, count]
              · simpa [Outcome.prepend, eventsWorld] using endpoint

 theorem exhaustiveRun_correspondence (prior : Prior) (fuel : Nat) (source : Source)
    (state : Snapshot) (out : Outcome) (world : World Bool Primitive)
    (represented : Reifies world state) (member : out ∈ exhaustiveRun fuel source state)
    (completed : out.status = .completed) :
    source.quote.WellFormed ∧
      Steps (context prior) out.events.length (some source.quote) world none
        (eventsWorld world out.events) ∧
      Reifies (eventsWorld world out.events) out.state ∧ out.events.length ≤ fuel := by
  unfold exhaustiveRun at member
  split at member
  · rename_i valid
    obtain ⟨steps, repr, bound, terminal⟩ := explore_correspondence prior fuel (some source) state out world represented member
    exact ⟨(Program.wellFormedCheck_iff _).mp valid, by simpa [terminal completed] using steps, repr, bound⟩
  · simp only [List.mem_singleton] at member
    subst out
    cases completed

 theorem exhaustiveRun_coverage (prior : Prior) (fuel : Nat) (source : Source)
    (state : Snapshot) (world after : World Bool Primitive) (n : Nat)
    (wellFormed : source.quote.WellFormed) (represented : Reifies world state)
    (steps : Steps (context prior) n (some source.quote) world none after)
    (bound : n ≤ fuel) :
    ∃ out ∈ exhaustiveRun fuel source state,
      out.status = .completed ∧ out.residual = none ∧ out.events.length = n ∧
      eventsWorld world out.events = after := by
  have valid := (Program.wellFormedCheck_iff source.quote).mpr wellFormed
  simpa [exhaustiveRun, valid] using explore_coverage prior fuel (some source) state world after n represented steps bound

/-- Admission is explicitly required only for the public executes wrapper. -/
 theorem exhaustiveRun_executes (prior : Prior) (fuel : Nat) (source : Source)
    (state : Snapshot) (out : Outcome) (world : World Bool Primitive)
    (represented : Reifies world state) (admitted : Admitted (context prior).model.dynamics world)
    (member : out ∈ exhaustiveRun fuel source state) (completed : out.status = .completed) :
    executes (context prior) source.quote world (eventsWorld world out.events) := by
  obtain ⟨wellFormed, steps, _, _⟩ := exhaustiveRun_correspondence prior fuel source state out world represented member completed
  exact ⟨wellFormed, admitted, out.events.length, steps⟩

/-- Deterministic replay also carries a literal reference prefix witness. -/
 theorem replay_correspondence (prior : Prior) (schedule : List Nat)
    (source : Option Source) (state : Snapshot) (world : World Bool Primitive)
    (represented : Reifies world state) :
    let out := replay schedule source state
    Steps (context prior) out.events.length (source.map Source.quote) world
      (out.residual.map Source.quote) (eventsWorld world out.events) ∧
      Reifies (eventsWorld world out.events) out.state ∧
      out.events.length ≤ schedule.length ∧
      (out.status = .completed → out.residual = none) := by
  induction schedule generalizing source state world with
  | nil =>
      cases source <;> simp only [replay]
      all_goals exact ⟨.refl _ _, represented, by simp, by simp⟩
  | cons choice rest ih =>
      cases source with
      | none => exact ⟨.refl _ _, represented, by simp [replay], by simp [replay]⟩
      | some source =>
          cases h : nextAll source state with
          | nil =>
              simp only [replay, h]
              exact ⟨.refl _ _, represented, by simp, by simp⟩
          | cons first nexts =>
              cases get : (first :: nexts)[choice]? with
              | none =>
                  simp only [replay, h, get]
                  exact ⟨.refl _ _, represented, by simp, by simp⟩
              | some next =>
                  have member : next ∈ nextAll source state := by
                    rw [h]
                    exact List.mem_of_getElem? get
                  obtain ⟨step, repr⟩ := nextAll_correspondence prior source state next world represented member
                  obtain ⟨steps, finalRepr, bound, terminal⟩ := ih next.1 next.2.state
                    (eventWorld world next.2) repr
                  simp only [replay, h, get]
                  refine ⟨?_, ?_, ?_, terminal⟩
                  · simpa [Outcome.prepend, eventsWorld] using Steps.cons step steps
                  · simpa [Outcome.prepend, eventsWorld] using finalRepr
                  · simpa [Outcome.prepend] using Nat.succ_le_succ bound

 theorem scheduledRun_correspondence (prior : Prior) (schedule : List Nat)
    (source : Source) (state : Snapshot) (world : World Bool Primitive)
    (represented : Reifies world state)
    (completed : (scheduledRun schedule source state).status = .completed) :
    source.quote.WellFormed ∧
      Steps (context prior) (scheduledRun schedule source state).events.length
        (some source.quote) world none
        (eventsWorld world (scheduledRun schedule source state).events) ∧
      Reifies (eventsWorld world (scheduledRun schedule source state).events)
        (scheduledRun schedule source state).state := by
  by_cases valid : source.quote.wellFormedCheck = true
  · simp only [scheduledRun, valid, if_true] at completed ⊢
    obtain ⟨steps, repr, _, terminal⟩ := replay_correspondence prior schedule (some source) state world represented
    exact ⟨(Program.wellFormedCheck_iff _).mp valid, by simpa [terminal completed] using steps, repr⟩
  · simp [scheduledRun, valid] at completed

 theorem scheduledRun_executes (prior : Prior) (schedule : List Nat)
    (source : Source) (state : Snapshot) (world : World Bool Primitive)
    (represented : Reifies world state) (admitted : Admitted (context prior).model.dynamics world)
    (completed : (scheduledRun schedule source state).status = .completed) :
    executes (context prior) source.quote world
      (eventsWorld world (scheduledRun schedule source state).events) := by
  obtain ⟨wellFormed, steps, _⟩ := scheduledRun_correspondence prior schedule source state world represented completed
  exact ⟨wellFormed, admitted, _, steps⟩

end

/-- Command order is extracted from emitted commands, never a supplied report. -/
def Outcome.commandCodes (out : Outcome) : List Nat :=
  out.events.filterMap fun event => event.emission.map Command.code

namespace Smoke

open Lara.Examples.BHLExecution (report oldReport x y dataId aliasId
  repeatedTests reportOnly terminatingLoop parallel undefinedBranch incrementX incrementY badParallel)

def initial : Snapshot := Lara.Examples.BHLBinaryModel.initialSnapshot true false

def aliases : Outcome := scheduledRun [0, 0, 0] repeatedTests initial
def report : Outcome := scheduledRun [0] reportOnly initial
def single : Outcome := scheduledRun [0]
  (Lara.Examples.BHLBinaryRuns.singleSource Lara.Examples.BHLBinaryModel.firstId) initial
def accounted : Outcome := scheduledRun [0, 0] Lara.Examples.BHLBinaryRuns.pairSource initial
def hidden : Outcome := scheduledRun [0, 0] Lara.Examples.BHLBinaryRuns.hiddenSource initial
def loop : Outcome := scheduledRun (List.replicate 7 0) terminatingLoop initial
def left : Outcome := scheduledRun [0, 0] parallel initial
def right : Outcome := scheduledRun [1, 0] parallel initial

/-- Root-left/child-right is successor index 1, not either uniform Bool choice. -/
def nested : Source := .par (.par incrementX incrementY) (.command .skip)
def mixed : Outcome := scheduledRun [1, 0, 0] nested initial
def nestedAll : List Outcome := exhaustiveRun 3 nested initial
def exhausted : Outcome := scheduledRun [] terminatingLoop initial
def undefined : Outcome := scheduledRun [0] undefinedBranch initial
def malformed : Outcome := scheduledRun [0, 0] badParallel initial
def boundedLoop : List Outcome := exhaustiveRun 6 terminatingLoop initial

theorem nested_successor_codes :
    (nextAll nested initial).map (fun out => out.2.emission.map Command.code) =
      [some 110, some 111, some 0] := by rfl

theorem terminal_zero :
    (replay [] none initial).status = .completed := by rfl

theorem nonterminal_zero : exhausted.status = .incomplete := by rfl

theorem completed_cases :
    aliases.status = .completed ∧ report.status = .completed ∧
    single.status = .completed ∧ accounted.status = .completed ∧
    hidden.status = .completed ∧ loop.status = .completed ∧
    left.status = .completed ∧ right.status = .completed ∧
    mixed.status = .completed := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mixed_command_order : mixed.commandCodes = [111, 110, 0] := by rfl

theorem all_nested_orders : (nestedAll.map Outcome.commandCodes).Perm
    [[110, 111, 0], [110, 0, 111], [111, 110, 0],
      [111, 0, 110], [0, 110, 111], [0, 111, 110]] := by exact List.Perm.refl _

theorem undefined_guard : undefined.status = .failed .undefinedStep := by rfl

theorem malformed_parallel : malformed.status = .failed .malformedSource := by decide

theorem fuel_exhaustion : boundedLoop.map Outcome.status = [.incomplete] := by rfl

theorem repeated_full_ledger :
    aliases.state.ledger =
      (initial.ledger + {(true, Lara.Examples.BHLExecution.Science.correctId)}) +
        {(true, Lara.Examples.BHLExecution.Science.correctId)} := by rfl

theorem pvalue_no_ledger : report.state.ledger = initial.ledger := by rfl

theorem protected_old_report :
    aliases.state.rationals Lara.Examples.BHLExecution.oldReport.id = some (7 / 11 : ℚ) := by rfl

theorem calibrated_report :
    single.state.rationals Lara.Examples.BHLExecution.report.id =
      some (Tests.Binary.pvalue true) := by rfl

end Smoke
end Lara.BHL.FiniteExecution
