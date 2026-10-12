import Lara.Surface.Check
import Lara.Driver
import Lara.Evidence.Types
import Lara.BHL.BridgeSource

namespace Lara.Process.Source

/-- Authored wire identity, including unsupported versions for typed rejection.
Only Driver.coreVersionText is compatible with the production observer. -/
structure CoreVersion where
  val : String
  deriving DecidableEq

/-- Authored backend version, not an extensible implementation registry. -/
structure BackendVersion where
  val : String
  deriving DecidableEq

structure BackendIdentity where
  name : Presentation.BackendId
  version : BackendVersion
  deriving DecidableEq

structure ReplayIdentity where
  core : CoreVersion
  policy : Presentation.PolicyId
  backends : List BackendIdentity
  theories : List Presentation.TheoryDigest
  artifact : Presentation.Digest
  deriving DecidableEq

/-- Captures are input evidence, never an observation fabricated by replay. -/
structure EvidenceCapture where
  snapshot : Evidence.Snapshot
  manifest : List Evidence.ObjectMeta
  deriving DecidableEq

structure SourceInput where
  surface : Surface.Input
  replay : ReplayIdentity
  capture : Option EvidenceCapture
  deriving DecidableEq

/-- The registry and parser are fixed production operations, not caller inputs. -/
def sourceEnv (input : SourceInput) : Surface.Env canonNum where
  registry := Driver.buildRegistry (input.surface.policy.theories.map fun entry =>
    (Surface.toSupportTheoryDigest entry.1, entry.2))
  startsIdent := fun source =>
    if source.isNat then false else Surface.sourceStartsIdentifier source
  startsIdent_nat_false := by intro n; simp
  encodeProp := fun text =>
    (Surface.parseSurfaceProp text).map fun proposition =>
      Strict.encodeAtomKey (nf canonNum proposition)

inductive ReplayError where
  | unsupportedCore : CoreVersion → ReplayError
  | policyMismatch
  | backendMismatch
  | duplicateBackend
  | unsupportedBackend : BackendIdentity → ReplayError
  | duplicateTheory
  | theoryMismatch
  | artifactMismatch
  deriving DecidableEq

def BackendIdentity.entry (backend : BackendIdentity) : Presentation.BackendEntry :=
  (backend.name, backend.version.val)

def supportedBackend (backend : BackendIdentity) : Bool :=
  Driver.supportedBackends.contains (backend.name.val, backend.version.val)

/-- Closed compatibility checks precede semantic observation. Theory identity uses
production code-point sorting; declarations retain their original source order. -/
def replayCompatible (input : SourceInput) : Except ReplayError _root_.Unit := do
  if input.replay.core.val != Driver.coreVersionText then
    throw (.unsupportedCore input.replay.core)
  if input.replay.policy != input.surface.policy.id ||
      input.surface.program.policy != input.surface.policy.id then
    throw .policyMismatch
  if input.replay.backends.map BackendIdentity.entry != input.surface.program.backends then
    throw .backendMismatch
  if !(decide (input.replay.backends.map (·.name)).Nodup) then
    throw .duplicateBackend
  match input.replay.backends.find? (fun backend => !supportedBackend backend) with
  | some backend => throw (.unsupportedBackend backend)
  | none => pure ()
  let theories := input.surface.policy.theories.map (fun entry => entry.1.val)
  if !(decide theories.Nodup) then throw .duplicateTheory
  if input.replay.theories.map (·.val) != Driver.sortCodePointStrings theories then
    throw .theoryMismatch
  if input.replay.artifact != input.surface.program.digest then
    throw .artifactMismatch
  pure ()

end Lara.Process.Source
