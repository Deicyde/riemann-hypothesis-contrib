/- Use stock Lake to calculate traces, retaining only attested theorem artifacts. -/
module
import Lake
import Lake.CLI.Main
import Lake.Load.Workspace
import all Lake.Build.Module
import SplitData
import all Lean.Shell

open Lean Lake System

private def load (root : String) : IO Workspace := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let cfg ← (({
    rootDir := root
    updateToolchain := false
    elanInstall? := elanInstall?
    leanInstall? := leanInstall?
    lakeInstall? := lakeInstall?
  } : LakeOptions).mkLoadConfig).toIO (IO.userError ∘ toString)
  let some ws ← (loadWorkspace cfg).toBaseIO | throw <| IO.userError "cannot load workspace"
  return ws

private def roots (ws : Workspace) : IO (Array Lake.Module) := do
  let mut modules := #[]
  for lib in ws.root.leanLibs do
    if ws.root.defaultTargets.contains lib.name then
      modules := modules ++ (← lib.getModuleArray)
  return modules.qsort (fun a b => a.name.quickLt b.name)

private structure PlanState where
  seen : NameSet := {}
  visiting : NameSet := {}
  lean : Std.HashMap (Name × Bool × Bool × Bool) Bool := {}

private abbrev PlanM := StateRefT PlanState FetchM

-- This is the IR-phase propagation from Lean.importModulesCore, specialized to
-- a module-system root. Only the existence of a runtime Lean import is needed
-- by the stock initialization-only C emitter.
private partial def usesLean (name : Name) (all data irMeta : Bool) : PlanM Bool := do
  let key := (name, all, data, irMeta)
  if let some b := (← get).lean[key]? then return b
  if (`Lean).isPrefixOf name && (all || !irMeta) then return true
  let ws ← getWorkspace
  let some mod := ws.findModule? name | return false
  let header ← (← mod.header.fetch).await
  let mut found := false
  for imp in header.imports do
    let data := data && (imp.isExported || all)
    let all := all && imp.importAll
    let irMeta := irMeta || (data && imp.isMeta)
    if data || irMeta || all then
      if ← usesLean imp.module all data irMeta then
        found := true
        break
  modify fun s => {s with lean := s.lean.insert key found}
  return found

private partial def planModule (mod : Lake.Module) (raw : FilePath)
    (out : IO.FS.Handle) : PlanM Unit := do
  if (← get).seen.contains mod.name then return
  if (← get).visiting.contains mod.name then error "cyclic imports"
  modify fun s => {s with visiting := s.visiting.insert mod.name}
  let ws ← getWorkspace
  let input ← (← mod.input.fetch).await
  unless input.header.isModule do error s!"{mod.name}: expected module-system source"
  unless mod.lib.extraDepTargets.isEmpty && mod.lib.config.needs.isEmpty &&
      mod.pkg.extraDepTargets.isEmpty && !mod.shouldPrecompile &&
      !mod.shouldPrecompileImports && mod.pkg.externLibs.isEmpty &&
      mod.dynlibs.isEmpty && mod.plugins.isEmpty do
    error s!"{mod.name}: unsupported native build dependencies"
  for imp in input.header.imports do
    if let some dep := ws.findModule? imp.module then
      if dep.pkg.keyName == ws.root.keyName then planModule dep raw out
  let mut runtimeLean := false
  for imp in input.header.imports do
    if ← usesLean imp.module imp.importAll true imp.isMeta then runtimeLean := true
  let imports := input.header.imports.map fun imp => Json.mkObj [
    ("module", toJson imp.module),
    ("package", toJson ((ws.findModule? imp.module).bind (·.pkg.id?)))]
  let relative := mod.name.toString.replace "." "/"
  out.putStrLn (Json.mkObj [
    ("name", toJson mod.name), ("package", toJson mod.pkg.id?),
    ("archivedName", toJson (Name.str .anonymous "src" ++ mod.name)),
    ("source", toJson mod.relLeanFile),
    ("input", toJson (raw / (relative ++ ".olean"))),
    ("olean", toJson mod.oleanFile), ("ilean", toJson mod.ileanFile),
    ("c", toJson mod.cFile), ("trace", toJson mod.traceFile),
    ("imports", toJson imports), ("sourceImports", toJson input.header.imports),
    ("usesLean", toJson runtimeLean)]).compress
  modify fun s => {s with
    seen := s.seen.insert mod.name
    visiting := s.visiting.erase mod.name}

private def plan (ws : Workspace) (raw out : FilePath) : IO Unit := do
  let stream ← IO.FS.Handle.mk out .write
  let modules ← roots ws
  let action : PlanM Unit := do
    for mod in modules do planModule mod raw stream
  let (_, s) ← ws.runFetchM (action.run {}) {verbosity := .quiet, noBuild := true, trustHash := false}
  IO.println s!"planned {s.seen.size} split modules"

private unsafe def index (ws : Workspace) (jobs classifications frozen report runtimeTool : FilePath)
    (compileRuntime : Bool := true) : IO Unit := do
  let mut runtime : NameSet := {}
  for line in (← IO.FS.lines classifications) do
    let .ok j := Json.parse line | throw <| IO.userError "invalid classification"
    let .ok name := j.getObjValAs? String "name" | throw <| IO.userError "missing classification name"
    let .ok b := j.getObjValAs? Bool "needsCompile" | throw <| IO.userError "missing classification flag"
    if b then runtime := runtime.insert name.toName
  let input ← IO.FS.Handle.mk jobs .read
  let output ← IO.FS.Handle.mk report .write
  let action : FetchM Unit := do
    repeat
      let line ← input.getLine
      if line.isEmpty then break
      let .ok j := Json.parse line | error "invalid import job"
      let .ok name := j.getObjValAs? String "name" | error "missing module name"
      let some mod := ws.findModule? name.toName | error "unknown module"
      let presetup ← (← mod.presetup.fetch).await
      if compileRuntime && runtime.contains mod.name then
        let .ok archivedName := j.getObjValAs? Name "archivedName" | error "missing archived name"
        let .ok source := j.getObjValAs? String "source" | error "missing source filename"
        let setup ← mkModuleSetup mod presetup
        let setup := {setup with name := archivedName}
        let work := frozen / "runtime-checks" / name.replace "." "/"
        IO.FS.createDirAll work
        let setupFile := work / "setup.json"
        let olean := work / "fresh.olean"
        let ilean := work / "fresh.ilean"
        let c := work / "fresh.c"
        IO.FS.writeFile setupFile (toJson setup).pretty
        proc {cmd := runtimeTool.toString, args := #[name, source, setupFile.toString,
          olean.toString, ilean.toString, c.toString]}
        let old := frozen / name.replace "." "/"
        SplitCacheImport.attest mod.name old (work / "fresh") (work / "comparison")
        -- Accept only C. The archived kernel proofs, private identities, and IR
        -- remain exactly the normalized copies previously installed.
        if let some parent := mod.cFile.parent then IO.FS.createDirAll parent
        let temporary := mod.cFile.addExtension "importing"
        IO.FS.writeBinFile temporary (← IO.FS.readBinFile c)
        IO.FS.rename temporary mod.cFile
        IO.FS.removeDirAll work
      unless ← mod.checkArtifactsExist true false do
        error s!"{name}: incomplete artifacts; runtime modules must be rebuilt first"
      let arts ← mod.computeArtifacts true false
      let temporary := mod.traceFile.addExtension "importing"
      IO.FS.writeFile temporary (toJson (BuildMetadata.ofFetch presetup.trace.hash (toJson arts.descrs))).compress
      IO.FS.rename temporary mod.traceFile
      output.putStrLn (Json.mkObj [("name", toJson name),
        ("input", toJson presetup.trace.hash.toString),
        ("runtime_source_checked", toJson (compileRuntime && runtime.contains mod.name)),
        ("proof_artifacts_reused", toJson true)]).compress
      output.flush
  ws.runFetchM action {verbosity := .quiet, noBuild := true, trustHash := false}

/-- Resolve import paths from normalized OLean/IR files without requiring C or
claiming a complete Lake build. No traces or cache archives are written here. -/
private def setups (ws : Workspace) (jobs classifications work report : FilePath) : IO Unit := do
  let mut selected : NameSet := {}
  for line in (← IO.FS.lines jobs) do
    let .ok j := Json.parse line | throw <| IO.userError "invalid import job"
    let .ok name := j.getObjValAs? Name "name" | throw <| IO.userError "missing module name"
    selected := selected.insert name
  let mut runtime : NameSet := {}
  for line in (← IO.FS.lines classifications) do
    let .ok j := Json.parse line | throw <| IO.userError "invalid classification"
    let .ok name := j.getObjValAs? Name "name" | throw <| IO.userError "missing classification name"
    let .ok b := j.getObjValAs? Bool "needsCompile" | throw <| IO.userError "missing classification flag"
    if b then runtime := runtime.insert name
  let root := ws.root.keyName
  let cfg : ModuleFacetConfig Module.elabArtsFacet := mkFacetJobConfig fun mod => do
    unless mod.pkg.keyName == root do return ← Module.elabArtsFacetConfig.run mod
    unless selected.contains mod.name do error s!"unplanned root import {mod.name}"
    Job.async do
      -- Source/module metadata still comes exclusively from stock Lake.
      -- Only this planning workspace permits an absent C artifact.
      let arts ← mod.computeArtifacts true true
      return {arts with
        irSig? := some (← computeArtifact mod.irSigFile "ir.sig" (text := false))
        ir? := some (← computeArtifact mod.irFile "ir" (text := false))}
  let ws := ws.addModuleFacetConfig cfg
  let output ← IO.FS.Handle.mk report .write
  let action : FetchM Unit := do
    for line in (← IO.FS.lines jobs) do
      let .ok j := Json.parse line | error "invalid import job"
      let .ok name := j.getObjValAs? Name "name" | error "missing module name"
      unless runtime.contains name do continue
      let some mod := ws.findModule? name | error "unknown module"
      let presetup ← (← mod.presetup.fetch).await
      let .ok archivedName := j.getObjValAs? Name "archivedName" | error "missing archived name"
      let setup ← mkModuleSetup mod presetup
      let dir := work / name.toString.replace "." "/"
      IO.FS.createDirAll dir
      let path := dir / "setup.json"
      IO.FS.writeFile path (toJson {setup with name := archivedName}).pretty
      output.putStrLn (Json.mkObj [("name", toJson name), ("setup", toJson path),
        ("input", toJson presetup.trace.hash.toString)]).compress
      output.flush
  ws.runFetchM action {verbosity := .quiet, noBuild := true, trustHash := false}

public unsafe def main (args : List String) : IO Unit := do
  Internal.setThreadStackSize (400000 * 1024)
  match args with
  | ["plan", root, raw, jobs] => plan (← load root) raw jobs
  | ["index", root, jobs, classifications, frozen, report, runtimeTool] =>
    index (← load root) jobs classifications frozen report runtimeTool
  | ["index-ready", root, jobs, classifications, report] =>
    index (← load root) jobs classifications "" report "" false
  | ["setups", root, jobs, classifications, work, report] =>
    setups (← load root) jobs classifications work report
  | _ => throw <| IO.userError "expected plan ROOT RAW JOBS | index ROOT JOBS CLASSIFICATIONS FROZEN REPORT RUNTIME_TOOL | setups ROOT JOBS CLASSIFICATIONS WORK REPORT | index-ready ROOT JOBS CLASSIFICATIONS REPORT"
