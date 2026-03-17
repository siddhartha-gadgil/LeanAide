import Lean
-- import LeanAideCore.Kernel
-- import LeanAideCore.Syntax.Kernel

open Lean Meta Elab Term PrettyPrinter Tactic Command Parser

namespace LeanAide

syntax (name := quoteCommand) docComment "#quote" ppSpace (ident)? ("<|" term ";")? : command

macro_rules
| `(command|$doc:docComment #quote $n:ident) =>
  let text := doc.raw.reprint.get!
  let text := text.drop 4 |>.dropEnd 4
  let textStx := Syntax.mkStrLit text.toString
  `(command| def $n := $textStx)
| `(command|$doc:docComment #quote) =>
  let text := doc.raw.reprint.get!
  let text := text.drop 4 |>.dropEnd 4
  let textStx := Syntax.mkStrLit text.toString
  `(command| example := $textStx)
| `(command|$doc:docComment #quote $n:ident <| $t:term ;) =>
  let text := doc.raw.reprint.get!
  let text := text.drop 4 |>.dropEnd 4
  let textStx := Syntax.mkStrLit text.toString
  `(command| def $n := $t $textStx)
| `(command|$doc:docComment #quote <|$t:term ;) =>
  let text := doc.raw.reprint.get!
  let text := text.drop 4 |>.dropEnd 4
  let textStx := Syntax.mkStrLit text.toString
  `(command| example := $t $textStx)


def mkQuoteCmd (doc: String) (name?: Option Name) : CoreM <| Syntax.Command := do
  let docs := mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom ("\n" ++ doc ++ "\n" ++ " -/")]
  match name? with
  | none =>
    `(command| $docs:docComment #quote)
  | some name =>
  let ident := mkIdent name
  `(command| $docs:docComment #quote $ident)


declare_syntax_cat filepath
syntax str : filepath
syntax filepath ppSpace "/" ppSpace str : filepath

partial def filePath : TSyntax `filepath → System.FilePath
  | `(filepath| $s:str) => s.getString
  | `(filepath| $fs:filepath / $s) => (filePath fs / s.getString)
  | _ => System.FilePath.mk ""


syntax (name:= loadFile) "#load_file" (ppSpace ident)? (ppSpace filepath)? : command
@[command_elab loadFile] def loadFileImpl : CommandElab := fun stx  =>
 Command.liftTermElabM  do
  match stx with
  | `(command| #load_file $id:ident $file) =>
    let filePath : System.FilePath := filePath file
    let content ← try
        IO.FS.readFile filePath
      catch _ =>
        if ← filePath.isDir then
          let files ← filePath.readDir
          let files := files.map (·.fileName)
          for f in files do
            let name := Syntax.mkStrLit f
            let newPath ← `(filepath| $file / $name)
            let newCommand ← `(command| #load_file $id $newPath)
            TryThis.addSuggestion stx newCommand
        else
          logWarning s!"Failed to read file: {filePath}"
        return
    let content := "\n" ++ content.trimAscii ++ "\n"
    let name := id.getId
    let textCmd ← mkQuoteCmd content name
    TryThis.addSuggestion (header := "Load source:\n") stx textCmd
  | `(command| #load_file $file:filepath) =>
    let filePath : System.FilePath := filePath file
    let content ← try
        IO.FS.readFile filePath

      catch _ =>
        if ← filePath.isDir then
          let files ← filePath.readDir
          let files := files.map (·.fileName)
          for f in files do
            let name := Syntax.mkStrLit f
            let newPath ← `(filepath| $file / $name)
            let newCommand ← `(command| #load_file $newPath:filepath)
            TryThis.addSuggestion stx newCommand
        else
          logWarning s!"Failed to read file: {filePath}"
        return
    let content := "\n" ++ content.trimAscii ++ "\n"
    let name := filePath.fileName.getD "source"
    let textCmd ← mkQuoteCmd content name.toName
    TryThis.addSuggestion (header := "Load source:\n") stx textCmd
  | `(command| #load_file $id:ident) =>
    let filePath : System.FilePath := "."
    let files ← filePath.readDir
    let files := files.map (·.fileName)
    for f in files do
      let name := Syntax.mkStrLit f
      let newPath ← `(filepath| $name:str)
      let newCommand ← `(command| #load_file $id $newPath:filepath)
      TryThis.addSuggestion stx newCommand
  | `(command| #load_file) =>
    let filePath : System.FilePath := "."
    let files ← filePath.readDir
    let files := files.map (·.fileName)
    for f in files do
      let name := Syntax.mkStrLit f
      let newPath ← `(filepath| $name:str)
      let newCommand ← `(command| #load_file $newPath:filepath)
      TryThis.addSuggestion stx newCommand
  | _ => throwUnsupportedSyntax

-- #consider "Hello there."

declare_syntax_cat json_wrap
syntax json : json_wrap

def getJsonSyntax (js : Json) : MetaM <| TSyntax `json := do
  let .ok stx :=
    runParserCategory (← getEnv) `json_wrap js.pretty | throwError "Failed to parse JSON: {js}"
  match stx with
  | `(json_wrap| $j:json) =>
    return j
  | _ => throwError "Unexpected syntax: {stx}"

-- Test code
syntax (name:= rt_json) "#rt_json" ppSpace json : command

@[command_elab rt_json] def elabRtJsonImpl : CommandElab
| stx_cmd@`(command| #rt_json $js:json) =>
  Command.liftTermElabM do
  let tExp ← elabTerm (← `(json% $js)) (mkConst ``Json)
  Term.synthesizeSyntheticMVarsNoPostponing
  let term ← unsafe evalExpr Json (mkConst ``Json) tExp
  let stx ← getJsonSyntax term -- extract syntax from JSON
  logInfo m!"JSON Syntax: {stx}"
  let n := mkIdent `json_example
  let cmd ← `(command| def $n := json% $stx:json)
  logInfo m!"Command: {cmd}"
  TryThis.addSuggestion stx_cmd cmd
  logInfo m!"Done"
| _ => throwUnsupportedSyntax

-- #rt_json {"c": {"d": -3.4}, "b": [true, false, null], "a": 1}


end LeanAide
