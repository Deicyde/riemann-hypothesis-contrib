/-
Generate missing runtime C with the archive's declaration identities, while
using the canonical import name for its native module initializer. Fresh Lean
artifacts are temporary compatibility evidence; the archived proofs are kept.
-/
module
import Lean
import Lean.Elab.Frontend
import Lean.Compiler.LCNF.EmitC
import all Lean.Shell

open Lean System

public unsafe def main (args : List String) : IO UInt32 := do
  let [canonical, source, setupFile, olean, ilean, c] := args
    | throw <| IO.userError "expected canonical-name source setup olean ilean c"
  Internal.setThreadStackSize (400000 * 1024)
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let setup ← ModuleSetup.load setupFile
  let input ← IO.FS.readFile source
  let env? ← Elab.runFrontend input setup.options.toOptions source setup.name
    (trustLevel := 1) (oleanFileName? := some olean) (ileanFileName? := some ilean)
    (jsonOutput := true) (setup? := some setup)
  let some env := env? | return 1
  let data ← (Compiler.LCNF.emitC canonical.toName).toIO'
    {fileName := source, fileMap := default} {env}
  IO.FS.writeFile c data
  return 0
