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
    importModules (loadExts := true) #[{module := `Mathlib},
    {module:= `LeanAide.TheoremElab},
    {module:= `LeanCodePrompts.Translate},
    {module:= `LeanAide.AutoTactic},
    {module:= `LeanAide.StructToLean},
    {module:= `LeanAide.Syntax}] {}
  withUnpickle (← picklePath "docString")
    <|fun (docStringData : EmbedData) => do
  withUnpickle (← picklePath "description")
    <|fun (descData : EmbedData) =>  do
  withUnpickle (← picklePath "concise-description")
    <|fun (concDescData : EmbedData) => do
  let dataMap :
    EmbedMap := Std.HashMap.ofList [("docString", docStringData), ("description", descData), ("concise-description", concDescData)]
  let codeGen : CodeGenerator := {}
  let statement := args[0]!
  let core :=
    codeGen.statementToCode statement  |>.runWithEmbeddings dataMap
  let io? :=
    core.run {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 0, maxRecDepth := 1000000}
    {env := env}
  let io?' ← io?.toIO'
  match io?' with
  | Except.ok ((result, name), s) =>
    let messages := s.messages
    IO.eprintln "Ran successfully, with messages:"
    for msg in messages.toList do
      IO.eprintln (← msg.data.toString)
    let outFile := System.mkFilePath <| ["CodeGen", s!"{name}.lean"]
    IO.FS.writeFile outFile result.pretty
    IO.eprintln s!"Ran successfully, written to {outFile}"
    return 0
  | Except.error e =>
    do
      IO.eprintln "Ran with error"
      let msg ← e.toMessageData.toString
      IO.eprintln msg
      return 1
