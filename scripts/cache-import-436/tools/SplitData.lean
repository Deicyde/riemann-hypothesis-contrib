/-
Normalize only package metadata in independently attested split artifacts.
Read and write each sharing group together: split parts are not standalone files.
Input artifacts are immutable; all normalized artifacts go to another directory.
No target module is imported, initialized, or elaborated by this program.
-/
module
import all Lean.Environment
import all Lean.Compiler.ModPkgExt
public import Lean
import Lean.Compiler.LCNF.EmitC
import Lean.Linter.PersistentLintLog

open Lean System

namespace SplitCacheImport

private def str (j : Json) (key : String) : IO String :=
  match j.getObjValAs? String key with
  | .ok s => pure s
  | .error e => throw <| IO.userError e

private unsafe def normalizeData (data : ModuleData) (pkg : PkgId) : IO (ModuleData × Nat) := do
  let mut count := 0
  let mut rewritten := #[]
  for (name, entries) in data.entries do
    if name != modPkgExt.name then
      rewritten := rewritten.push (name, entries)
      continue
    unless entries.size == 1 do
      throw <| IO.userError "unexpected package-extension entry count"
    let some entry := entries[0]? | throw <| IO.userError "missing package entry"
    let actual : Option PkgId := unsafeCast entry
    if actual.isSome && actual != some pkg then
      throw <| IO.userError s!"unexpected archived package: {actual}"
    count := count + 1
    rewritten := rewritten.push (name, #[unsafeCast (some pkg : Option PkgId)])
  return ({data with entries := rewritten}, count)

private def hasRuntime (data : ModuleData) : Bool :=
  data.entries.any fun (name, es) =>
    !es.isEmpty && (name == `Lean.Compiler.LCNF.impureSigExt ||
      name == `Lean.IR.declMapExt || name == `Lean.regularInitAttr ||
      name == `Lean.builtinInitAttr || name == `Lean.Compiler.LCNF.postponedCompileDeclsExt)

@[noinline] private unsafe def writeGroup (mod : Name) (pkg : PkgId)
    (inputs outputs : Array FilePath) (expectedImports : Array Import)
    (writeOutputs : Bool) : IO (Bool × Array CompactedRegion) := do
  let parts ← readModuleDataParts inputs
  unless parts.all (·.1.isModule) do
    -- Lean's empty initial .ir.sig is the sole non-module part in a split group.
    let some (first, _) := parts[0]? | throw <| IO.userError "empty split group"
    unless parts.size == 2 && !first.isModule && first.imports.isEmpty &&
        first.constants.isEmpty && first.entries.isEmpty do
      throw <| IO.userError "expected split module-system artifacts"
  let some (last, _) := parts.back? | throw <| IO.userError "empty split group"
  unless last.imports == expectedImports do
    throw <| IO.userError "archive imports differ from source header"
  let runtime := parts.any (hasRuntime ·.1)
  let normalized ← parts.mapM fun (data, _) => normalizeData data pkg
  unless (normalized.foldl (fun n (_, c) => n + c) 0) > 0 do
    throw <| IO.userError "split group has no package metadata"
  if writeOutputs then
    for path in outputs do
      if let some dir := path.parent then IO.FS.createDirAll dir
    saveModuleDataParts mod (outputs.zip (normalized.map (·.1)))
  return (runtime, parts.map (·.2))

private unsafe def group (mod : Name) (pkg : PkgId)
    (inputs outputs : Array FilePath) (imports : Array Import) (writeOutputs : Bool) : IO Bool := do
  let (runtime, regions) ← writeGroup mod pkg inputs outputs imports writeOutputs
  -- All ModuleData references have died on return from the noinline helper.
  for region in regions.reverse do region.free
  return runtime

private def emitInit (mod : Name) (pkg : PkgId) (imports : Array Import)
    (j : Json) : IO String := do
  let .ok js := j.getObjValAs? (Array Json) "imports"
    | throw <| IO.userError "missing import package metadata"
  let mut packages : Std.HashMap Name (Option PkgId) := {}
  for imp in js do
    let name := (← str imp "module").toName
    let .ok p := imp.getObjValAs? (Option String) "package"
      | throw <| IO.userError "invalid import package metadata"
    packages := packages.insert name p
  let mut modules := imports.map fun imp =>
    ({imp with
      irPhases := if imp.importAll then .all else if imp.isMeta then .comptime else .runtime
      hasData := true} : EffectiveImport)
  let .ok usesLean := j.getObjValAs? Bool "usesLean"
    | throw <| IO.userError "missing runtime Lean import flag"
  if usesLean && !modules.any (fun m => (`Lean).isPrefixOf m.module && m.irPhases != .comptime) then
    modules := modules.push {module := `Lean, irPhases := .runtime, hasData := false}
  let (_, indices) := modules.foldl
    (init := ((0, {}) : Nat × Std.HashMap Name ModuleIdx)) fun (i, ns) imp =>
      (i + 1, ns.insert imp.module i)
  let importedPackages ← modules.mapM fun imp => do
    let p ← if !imp.hasData then pure none else do
      let some p := packages[imp.module]?
        | throw <| IO.userError s!"missing package for {imp.module}"
      pure p
    return #[p]
  let base ← mkEmptyEnvironment
  let kernel := private_decl% {base.toKernelEnv with
    header := {base.header with
      mainModule := mod
      isModule := true
      imports := imports
      modules := modules
      moduleName2Idx := indices}}
  let env := {base with base.private := kernel, checked := .pure kernel}
  let env := modPkgExt.toEnvExtension.setState env
    {importedEntries := importedPackages, state := some pkg}
  let (c, _) ← (Compiler.LCNF.emitC mod).toIO
    {fileName := "split cache import", fileMap := default} {env}
  return c

public unsafe def process (j : Json) (writeOutputs : Bool := true) : IO Json := do
  let name ← str j "name"
  let mod := name.toName
  let pkg ← str j "package"
  let input := FilePath.mk (← str j "input")
  let output := FilePath.mk (← str j "olean")
  let .ok imports := j.getObjValAs? (Array Import) "sourceImports"
    | throw <| IO.userError "missing source import declarations"
  let suffixes := #["", ".server", ".private"]
  let runtimeO ← group mod pkg
    (suffixes.map fun s => FilePath.mk (input.toString ++ s))
    (suffixes.map fun s => FilePath.mk (output.toString ++ s)) imports writeOutputs
  let irIn := input.withExtension "ir"
  let irOut := output.withExtension "ir"
  let runtimeIR ← group (mod ++ `ir) pkg
    #[irIn.addExtension "sig", irIn] #[irOut.addExtension "sig", irOut] imports writeOutputs
  let needsCompile := runtimeO || runtimeIR
  if writeOutputs && !needsCompile then
    let c := FilePath.mk (← str j "c")
    if let some dir := c.parent then IO.FS.createDirAll dir
    IO.FS.writeFile c (← emitInit mod pkg imports j)
  return Json.mkObj [("name", toJson name), ("needsCompile", toJson needsCompile)]

@[noinline] private unsafe def writeCanonical (mod : Name) (paths : Array FilePath)
    (outputs : Array FilePath) : IO (Array CompactedRegion) := do
  let parts ← readModuleDataParts paths
  let data := parts.map fun (data, _) =>
    {data with entries := data.entries.map fun (name, es) =>
      if name == `Lean.Linter.lintLogExt then
        let lints : Array Linter.LintEntry := unsafeCast es
        (name, unsafeCast (lints.map fun l =>
          {l with file := "<source>", message.fileName := "<source>"}))
      else (name, es)}
  saveModuleDataParts mod (outputs.zip data)
  return parts.map (·.2)

private unsafe def canonicalize (mod : Name) (paths : Array FilePath)
    (outputs : Array FilePath) : IO Unit := do
  let regions ← writeCanonical mod paths outputs
  for region in regions.reverse do region.free

/-- Compare every serialized entry, allowing only diagnostic lint filenames. -/
public unsafe def attest (mod : Name) (old fresh temporary : FilePath) : IO Unit := do
  IO.FS.createDirAll temporary
  for (name, suffixes) in #[(mod, #[".olean", ".olean.server", ".olean.private"]),
      (mod ++ `ir, #[".ir.sig", ".ir"])] do
    let paths (base : FilePath) := suffixes.map fun s => FilePath.mk (base.toString ++ s)
    let a := temporary / "archived"
    let b := temporary / "fresh"
    canonicalize name (paths old) (paths a)
    canonicalize name (paths fresh) (paths b)
    for suffix in suffixes do
      let a := FilePath.mk (a.toString ++ suffix)
      let b := FilePath.mk (b.toString ++ suffix)
      unless (← IO.FS.readBinFile a) == (← IO.FS.readBinFile b) do
        throw <| IO.userError s!"{mod}{suffix}: source rebuild differs from normalized archive"
      IO.FS.removeFile a
      IO.FS.removeFile b

end SplitCacheImport
