/- Pack only completed raw outputs verified by stock no-build trace checking. -/
module
import Lake
import all Lake.CLI.Main
import all Lake.Load.Workspace
import all Lake.Build.Module
import all Lake.Build.Run
open Lake Lean System

public def main (args : List String) : IO Unit := do
  let [root, jobs, report, overrides] := args
    | throw <| IO.userError "expected root jobs report package-overrides"
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let options : LakeOptions := {
    rootDir := root, configFile := "lakefile.toml", updateToolchain := false,
    elanInstall?, leanInstall?, lakeInstall?,
    packageOverrides := ← Manifest.loadEntries overrides
  }
  let config ← options.mkLoadConfig.toIO (IO.userError ∘ toString)
  let some ws ← (loadWorkspace config).toBaseIO
    | throw <| IO.userError "cannot load recovery workspace"
  let .ok names := Json.parse (← IO.FS.readFile jobs)
    | throw <| IO.userError "invalid recovery jobs"
  let .ok (names : Array String) := fromJson? names
    | throw <| IO.userError "invalid recovery module list"
  let output ← IO.FS.Handle.mk report .write
  let action : FetchM Unit := do
    for name in names do
      try
        let some mod := ws.findModule? name.toName | error s!"unknown module {name}"
        let row ← (← Job.async do
          -- noBuild=true forbids theorem elaboration and missing code generation.
          let arts ← (← mod.leanArts.fetch).await
          let .ok metadata := BuildMetadata.parse (← IO.FS.readFile mod.traceFile)
            | error "invalid completed module trace"
          let some descrs := metadata.outputs? | error "completed trace has no output hashes"
          let .ok (expected : ModuleOutputDescrs) := fromJson? descrs
            | error "invalid completed output description"
          let expected := toJson expected
          let actual := toJson arts.descrs
          for key in #["m", "o", "i", "rs", "r", "c", "b"] do
            if let .ok value := expected.getObjVal? key then
              let .ok got := actual.getObjVal? key | error s!"missing completed output {key}"
              unless got == value do error s!"completed output hash differs: {key}"
          -- An interrupted pack may leave arbitrary partial bytes. Never accept
          -- it by hashing: replace it with a fresh successful stock pack.
          if ← mod.ltarFile.pathExists then IO.FS.removeFile mod.ltarFile
          let packed ← mod.packLtar {arts with ltar? := none}
          let cached ← ws.lakeCache.saveArtifact packed.path "ltar"
          return Json.mkObj [("name", toJson name), ("ok", toJson true),
            ("input", toJson metadata.depHash.toString), ("artifact", toJson cached.descr.relPath.toString)]).await
        output.putStrLn row.compress
      catch _ =>
        output.putStrLn (Json.mkObj [("name", toJson name), ("ok", toJson false)]).compress
      output.flush
  ws.runFetchM action {verbosity := .quiet, noBuild := true, trustHash := false}
