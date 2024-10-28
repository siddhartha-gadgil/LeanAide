import Lean.Meta
import LeanCodePrompts
import LeanCodePrompts.BatchTranslate
import LeanAide.Config
import LeanAide.StructToLean
import Cli
open Lean Cli LeanAide.Meta LeanAide Translator

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

unsafe def main (args: List String) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  let env ←
    importModules #[{module := `Mathlib},
    {module:= `LeanAide.TheoremElab},
    {module:= `LeanCodePrompts.Translate}] {}
  withUnpickle (← picklePath "docString")
    <|fun (docStringData : EmbedData) => do
  withUnpickle (← picklePath "description")
    <|fun (descData : EmbedData) =>  do
  withUnpickle (← picklePath "concise-description")
    <|fun (concDescData : EmbedData) => do
  let dataMap :
    EmbedMap := HashMap.ofList [("docString", docStringData), ("description", descData), ("concise-description", concDescData)]
  let codeGen : CodeGenerator := {}
  let statement := args.get! 0
  let core :=
    codeGen.statementToCode statement  |>.runWithEmbeddings dataMap
  let io? :=
    core.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 0, maxRecDepth := 1000000}
    {env := env}
  let io?' ← io?.toIO'
  match io?' with
  | Except.ok result =>
    let hashCode := hash result.pretty
    let outFile := System.mkFilePath <| ["CodeGen", s!"from_statement_{hashCode}.lean"]
    IO.FS.writeFile outFile result.pretty
    IO.eprintln "Ran successfully"
    return 0
  | Except.error e =>
    do
      IO.eprintln "Ran with error"
      let msg ← e.toMessageData.toString
      IO.eprintln msg
      return 1
