module

public meta import Lean.Elab.Command
public meta import Mathlib.Util.VersoRoles
public import Mathlib.Init

/-!
# Citations of the bibliography

`@[cite "key"]` records that a declaration formalizes the entry `key` of `docs/references.bib`,
and `@[cite "key" "locator"]` that it formalizes a part of it, such as `"Theorem 2.3, p. 7"`. A
third string is a comment, such as `"proposed"` for a reference that has not been checked against
the statement. The attribute appends `[key], locator (comment)` to the docstring, which doc-gen4
links to the bibliography, and records the citation, which `citations` reads back.

A key must be nonempty and contain no whitespace, quotes, backslashes, braces, brackets or commas.
A key missing from `docs/references.bib` gets a warning. Lake does not track this read of the file,
so it only affects the warning.

The attribute runs after compilation, when a definition's own docstring has been written, so the
link is appended to that docstring. Mathlib's cross-reference attributes, such as `@[stacks]`, run
before elaboration and lose their link on a documented declaration, which is why this one does
not. A theorem's docstring is written on the theorem's own elaboration branch, so in the theorem's
own file the link is missing; files that import it see the link.

Mathlib has no attribute for citing its bibliography yet. If it gets one named `cite`, delete this
file and use that one.
-/

public meta section

open Lean Elab

namespace Lemmata.Cite

/-- A citation: the declaration `declName` formalizes the entry `key` of `docs/references.bib`,
or the part `locator` of it. -/
structure Citation where
  /-- The declaration that cites the entry. -/
  declName : Name
  /-- The key of the entry in `docs/references.bib`. -/
  key : String
  /-- The cited part of the entry, such as `Theorem 2.3`, or empty when all of it is cited. -/
  locator : String := ""
  /-- A comment on the citation, such as `proposed`, or empty. -/
  comment : String := ""
  deriving Inhabited, Repr

/-- The environment extension storing all citations. -/
initialize citeExt : SimplePersistentEnvExtension Citation (Array (Array Citation)) ←
  registerSimplePersistentEnvExtension {
    -- the imported citations are kept as they are, to avoid an overhead at initialization
    addImportedFn citations := citations
    addEntryFn citations _ := citations
  }

/-- Every citation: those of the imported modules, then those of the current one, in order. -/
def citations (env : Environment) : Array Citation :=
  let (currentModule, imported) := PersistentEnvExtension.getState citeExt env
  imported.flatten ++ currentModule.reverse.toArray

/-- Check that `key` can be cited, and warn when `docs/references.bib` lacks it. -/
def checkBibKey (key : String) : CoreM Unit := do
  if key.isEmpty || key.any fun (c : Char) => c.isWhitespace || "\"\\{}[],".contains c then
    throwError "Invalid key {repr key}: it must be nonempty, without whitespace or `\"\\\{}[],`."
  -- a file that cannot be read, such as a missing one, is skipped: it only affects the warning
  let .ok bib ← (IO.FS.readFile ("docs" / "references.bib")).toBaseIO | return
  unless Mathlib.VersoRoles.bibContainsKey bib key do
    logWarning m!"No bibliography entry `{key}` in `docs/references.bib`."

/-- Escape the ASCII punctuation in `s`, so that Markdown shows it as written. -/
def escapeFormatting (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    if c.toNat < 128 && !c.isAlphanum && !c.isWhitespace then acc.push '\\' |>.push c else acc.push c

/-- Append the paragraph `text` to the Markdown docstring of `decl`. -/
def appendDocString (decl : Name) (text : String) : CoreM Unit := do
  if doc.verso.get (← getOptions) then
    throwError "`@[cite]` only supports Markdown docstrings, not `doc.verso`."
  let oldDoc := (← findDocString? (← getEnv) decl).getD ""
  addDocStringCore decl ("\n\n".intercalate ([oldDoc, text].filter (· != "")))

/-- `@[cite "key"]`, `@[cite "key" "locator"]` or `@[cite "key" "locator" "comment"]` cites an
entry of `docs/references.bib`. -/
syntax (name := citeAttr) &"cite" ppSpace str (ppSpace str (ppSpace str)?)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `citeAttr
  descr := "Cite an entry of the bibliography `docs/references.bib`."
  add decl stx attrKind := do
    unless attrKind == .global do throwAttrMustBeGlobal `cite attrKind
    let `(attr| cite $key $[$locator $[$comment]?]?) := stx | throwUnsupportedSyntax
    let key' := key.getString
    let locator := (locator.map (·.getString)).getD ""
    let comment := (comment.join.map (·.getString)).getD ""
    withRef key <| checkBibKey key'
    -- doc-gen4 links a `[key]` of the bibliography, so the key is not escaped
    appendDocString decl <| s!"[{key'}]" ++
      (if locator.isEmpty then "" else s!", {escapeFormatting locator}") ++
      (if comment.isEmpty then "" else s!" ({comment})")
    modifyEnv (citeExt.addEntry · { declName := decl, key := key', locator, comment })
  applicationTime := .afterCompilation
}

end Lemmata.Cite
