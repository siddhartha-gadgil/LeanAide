import Lean.Meta
import LeanCodePrompts
import LeanCodePrompts.BatchTranslate
import LeanAide.PutnamBench
import LeanAide.Config
import LeanAide.PutnamBench
import Cli
open Lean Cli LeanAide.Meta LeanAide Translator Translate TranslateM

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← Lean.findSysroot) initFiles
  let translator : Translator := {}
  let translator : Translator := {translator with roundTrip := true, roundTripSelect := true}
  let dir := System.mkFilePath <| ["results", "putnam"]
  if !(← dir.pathExists) then
        IO.FS.createDirAll dir
  let start := args.get! 0 |>.toNat!
  let last := args.get! 1 |>.toNat!
  let outFile :=
        System.mkFilePath <| ["results", "putnam", s!"statements_{start}_{last}.jsonl"]
  let handle ← IO.FS.Handle.mk outFile IO.FS.Mode.append
  let env ←
    importModules #[{module := `Mathlib},
    {module:= `LeanAide.TheoremElab},
    {module:= `LeanCodePrompts.Translate},
    {module := `Mathlib}] {}
  withUnpickle (← picklePath "docString")
    <|fun (docStringData : EmbedData) => do
  withUnpickle (← picklePath "description")
    <|fun (descData : EmbedData) =>  do
  withUnpickle (← picklePath "concise-description")
    <|fun (concDescData : EmbedData) => do
  let dataMap :
    EmbedMap := Std.HashMap.ofList [("docString", docStringData), ("description", descData), ("concise-description", concDescData)]
  let mut jsLines : Array Json := #[]
  let mut successes : Array (String × Nat) := #[]
  let mut failures : Array (String × Nat) := #[]
  for l in [start:last] do
    if args.drop 2 |>.contains (toString l) then
      IO.eprintln s!"Skipping problem {l}"
    else
      let problem ←  putnamProblem l
      IO.eprintln s!"Starting problem {l}"
      let core := runToCore <|
        withEmbeddings dataMap do translator.translateM problem
      let io? :=
        core.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 100000000000, maxRecDepth := 1000000}
        {env := env}
      match ← io?.toIO' with
      | Except.ok (result, prompts) =>
        IO.eprintln "Success in running"
        IO.println "Prompts:"
        IO.println prompts.pretty
        IO.println "\n---\n"
        match result with
        | Except.ok succ =>
          IO.println "Success in elaboration"
          let js := toJson succ.toElabSuccessBase
          handle.putStrLn js.pretty
          IO.println js.pretty
          successes := successes.push (problem, l)
          jsLines := jsLines.push js
        | Except.error elabError =>
          do
            IO.println "Failed to elaborate"
            let js := toJson elabError
            handle.putStrLn js.pretty
            IO.println js.pretty
            failures := failures.push (problem, l)
            jsLines := jsLines.push js
        IO.eprintln s!"Written to file {outFile}"
      | Except.error e =>
        do
              IO.println "Ran with error"
              let msg ← e.toMessageData.toString
              IO.println msg
      IO.eprintln s!"Finished problem {l}"
      IO.eprintln s!"Successes: {successes.size}, Failures: {failures.size}"
  let js := toJson jsLines
  IO.FS.writeFile (System.mkFilePath <| ["results", "putnam", s!"statements_{start}_{last}.json"]) js.pretty
  IO.println "Successes:"
  for (problem, l) in successes do
    IO.println s!"{l}: {problem}"
  IO.println "Failures:"
  for (problem, l) in failures do
    IO.println s!"{l}: {problem}"
  return 0
