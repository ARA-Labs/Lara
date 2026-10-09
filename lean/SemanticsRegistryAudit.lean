import Lean
import Lara.Semantics.Registry

/-! Repository declaration coverage, separate from the open mathematical interface.
Compatible library modules share one environment and declaration scan. Conflicting
imports split into separate audits; standalone scripts remain isolated. -/
open Lean Meta

namespace SemanticsRegistryAudit

/-- Normalize type aliases, including explicit opaque aliases inspected as data.
Opaque expansion here is inventory inspection, not a kernel equality claim. -/
private def normalizeType (type : Expr) (fuel : Nat := 128) : MetaM Expr := do
  match fuel with
  | 0 => throwError "semantics audit: type alias expansion exhausted"
  | fuel + 1 =>
    let type ← withTransparency .all (whnf type)
    let .const name levels := type.getAppFn | return type
    let some (.opaqueInfo info) := (← getEnv).find? name | return type
    let value := info.value.instantiateLevelParams info.levelParams levels
    normalizeType (mkAppN value type.getAppArgs).headBeta fuel

private def isClosedSemantics (info : ConstantInfo) : MetaM Bool := do
  return (← normalizeType info.type).isConstOf ``Lara.Semantics.ExtensionSemantics

private def audit (targets : Array Name) : MetaM (Array (Name × Name)) := do
  let env ← getEnv
  let registry ← getConstInfo ``Lara.Semantics.Registry.semanticsInstance
  let some body := registry.value? | throwError "semantics registry has no inspectable object map"
  let mut registered : NameSet := {}
  for name in body.getUsedConstants do
    if ← isClosedSemantics (← getConstInfo name) then
      registered := registered.insert name
  if registered.isEmpty then
    throwError "semantics registry object map references no closed semantics"
  let requested : NameSet := targets.foldl (fun names name => names.insert name) {}
  let mut missing := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let target := env.header.moduleNames[idx.toNat]!
    if !requested.contains target then continue
    if (← isClosedSemantics info) && !registered.contains name then
      missing := missing.push (target, name)
  return missing.qsort (fun a b =>
    a.1.toString < b.1.toString ||
      (a.1 == b.1 && a.2.toString < b.2.toString))

end SemanticsRegistryAudit

private unsafe def auditModules (targets : Array Name) : IO Bool := do
  try
    -- Consume imported names before withImportModules releases compacted regions.
    return ← withImportModules
      ((targets.map fun target => { module := target }).push
        { module := `Lara.Semantics.Registry }) {} fun env => do
      let (missing, _) ← (SemanticsRegistryAudit.audit targets).run'.toIO
        { fileName := "<semantics-registry-audit>", fileMap := default }
        { env := env }
      for (target, name) in missing do
        IO.eprintln s!"semantics registry: unregistered closed declaration {name} (module {target})"
      return !missing.isEmpty
  catch ex =>
    -- Split conflicting imports regardless of filename. Single-module failures
    -- are reported without skipping the remaining requested modules.
    if targets.size ≤ 1 then
      IO.eprintln s!"semantics registry: cannot audit {targets[0]!}: {ex}"
      return true
    let middle := targets.size / 2
    let left ← auditModules (targets.extract 0 middle)
    let right ← auditModules (targets.extract middle targets.size)
    return left || right

unsafe def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: SemanticsRegistryAudit.lean MODULE..."
    return 2
  initSearchPath (← findSysroot)
  let (library, standalone) := args.partition fun name =>
    name == "Lara" || name.startsWith "Lara."
  let mut failed := false
  if !library.isEmpty then
    try
      failed ← auditModules (library.toArray.map String.toName)
    catch ex =>
      IO.eprintln s!"semantics registry: cannot audit library modules: {ex}"
      failed := true
  for arg in standalone do
    try
      failed := (← auditModules #[arg.toName]) || failed
    catch ex =>
      IO.eprintln s!"semantics registry: cannot audit {arg}: {ex}"
      failed := true
  if failed then return 1
  IO.println s!"Semantics registry audit passed ({args.length} modules)."
  return 0
