module
import SplitData
import all Lean.Shell
open Lean

public unsafe def main (args : List String) : IO Unit := do
  Internal.setThreadStackSize (400000 * 1024)
  if let ["compare", mod, old, fresh, temporary] := args then
    SplitCacheImport.attest mod.toName old fresh temporary
    return
  let (jobs, report, writeOutputs) ← match args with
    | ["classify", jobs, report] => pure (jobs, report, false)
    | [jobs, report] => pure (jobs, report, true)
    | _ => throw <| IO.userError "expected [classify] jobs.jsonl report.jsonl | compare MOD OLD FRESH TEMP"
  let input ← IO.FS.Handle.mk jobs .read
  let output ← IO.FS.Handle.mk report .write
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let .ok j := Json.parse line | throw <| IO.userError "invalid job"
    output.putStrLn (← SplitCacheImport.process j writeOutputs).compress
    output.flush
