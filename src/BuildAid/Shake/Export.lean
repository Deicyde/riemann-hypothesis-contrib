import Lean.Elab.Command
import Lean.Elab.Open

/-!
`export` that tells shake what it depends on.

An `export` alias leaves no trace in the oleans: a module that uses an exported name elaborates to
the target constant, so shake keeps the target's module and drops the file whose `export` made the
short name resolve. The `export` command itself also records nothing about its targets, so shake
can drop the imports that make them exist in the exporting file.

This elaborator takes precedence over the builtin one. It is `Lean.Elab.Command.elabExport`
(v4.33.1) with two records per exported name, using core's mechanism for dependencies that terms do
not show (`Lean/ExtraModUses.lean`):

* `recordIndirectModUse "export" declName`: a reference to `declName` from another module may also
  need this module (for the alias), so shake keeps this file for every module that uses the target
  and reached this file before;
* `recordExtraModUseFromDecl declName`: this module needs `declName`'s module, so shake keeps the
  imports that provide the targets.

It also records a use of its own module (`recordExtraModUseFromDecl` of `elabExport`), since nothing
else shows that a file needs this override; without it, shake would drop the import of this module
from exactly the files that run an `export`.
-/

namespace BuildAid.Shake.Export

open Lean Elab Command

/-- `export`, as `Lean.Elab.Command.elabExport`, also recording each target for shake. -/
@[command_elab Lean.Parser.Command.export]
def elabExport : CommandElab := fun stx => do
  let `(export $ns ($ids*)) := stx | throwUnsupportedSyntax
  let nss ← resolveNamespace ns
  let currNamespace ← getCurrNamespace
  if nss == [currNamespace] then throwError "invalid 'export', self export"
  let mut aliases := #[]
  for idStx in ids do
    let id := idStx.getId
    let declName ← resolveNameUsingNamespaces nss idStx
    if (← getInfoState).enabled then
      addConstInfo idStx declName
    aliases := aliases.push (currNamespace ++ id, declName)
    -- shake: importers using the alias need this module; this module needs the target's module
    recordIndirectModUse "export" declName
    recordExtraModUseFromDecl declName (isMeta := false)
  modify fun s => { s with env := aliases.foldl (init := s.env) fun env p => addAlias env p.1 p.2 }
  -- shake: this file needs this override
  -- (a single-backtick name: the constant does not exist yet while this body is elaborated)
  recordExtraModUseFromDecl `BuildAid.Shake.Export.elabExport (isMeta := false)

end BuildAid.Shake.Export
