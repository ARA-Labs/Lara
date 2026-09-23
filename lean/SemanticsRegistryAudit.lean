import Lean
import Lara.Semantics.Registry

/-! Repository declaration coverage, separate from the open mathematical interface.
Each requested module gets a fresh environment so executable `main` declarations
cannot collide. Registration names come from the core object map's actual body. -/
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

private def audit (target : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let registry ← getConstInfo ``Lara.Semantics.Registry.semanticsInstance
  let some body := registry.value? | throwError "semantics registry has no inspectable object map"
  let mut registered : NameSet := {}
  for name in body.getUsedConstants do
    if ← isClosedSemantics (← getConstInfo name) then
      registered := registered.insert name
  if registered.isEmpty then
    throwError "semantics registry object map references no closed semantics"
  let mut missing := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    if env.header.moduleNames[idx.toNat]! != target then continue
    if (← isClosedSemantics info) && !registered.contains name then
      missing := missing.push name
  return missing.qsort (fun a b => a.toString < b.toString)

end SemanticsRegistryAudit

unsafe def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: SemanticsRegistryAudit.lean MODULE..."
    return 2
  initSearchPath (← findSysroot)
  let mut failed := false
  for arg in args do
    let target := arg.toName
    try
      -- Only a Bool escapes this callback: imported names and expressions are
      -- consumed before withImportModules releases their compacted regions.
      let moduleFailed ← withImportModules #[{ module := target },
        { module := `Lara.Semantics.Registry }] {} fun env => do
        let (missing, _) ← (SemanticsRegistryAudit.audit target).run'.toIO
          { fileName := "<semantics-registry-audit>", fileMap := default }
          { env := env }
        for name in missing do
          IO.eprintln s!"semantics registry: unregistered closed declaration {name} (module {target})"
        return !missing.isEmpty
      failed := failed || moduleFailed
    catch ex =>
      IO.eprintln s!"semantics registry: cannot audit {target}: {ex}"
      failed := true
  if failed then return 1
  IO.println s!"Semantics registry audit passed ({args.length} modules)."
  return 0
