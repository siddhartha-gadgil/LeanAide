import Lean.Meta
import LeanCodePrompts.Translate
import LeanAide.Config
import LeanAide.TranslatorParams
import Cli
import LeanAide.Actor
import LeanAide.StructToLean
import LeanAideCore.TaskStatus
open Lean Cli LeanAide.Meta LeanAide Translator

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

unsafe def process_loop (env: Environment)(getLine : IO String) (putStrLn : String → IO Unit)
    (translator : Translator) (dataMap : EmbedMap) (states : TasksState) (chains : Json → Json → Array (Json → TranslateM Json)) : IO UInt32 := do
  IO.eprintln "Server ready. Waiting for input..."
  let inp ← getLine
  if inp.trim.isEmpty then
    process_loop env getLine putStrLn translator dataMap states chains
  else
  match Json.parse inp with
  | Except.error e =>
     IO.eprintln s!"Error parsing input: {e}"
     process_loop env getLine putStrLn translator dataMap states chains
  | Except.ok js =>
    let mode? := js.getObjValAs? String "mode" |>.toOption
    let ctx: Core.Context := {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 0, maxRecDepth := 1000000}
    match mode? with
    | some "async" =>
      IO.eprintln "Running in background"
      let hash := hash js
      states.addStart hash js
      let callback (js res : Json) : IO Unit := do
        IO.eprintln s!"Background process completed for token: {hash}\ninput: {js.pretty}"
        IO.eprintln s!"Output: {res.pretty}"
        states.addResult hash res
      let prios :=
        (js.getObjValAs? Task.Priority "priority").toOption |>.getD Task.Priority.default
      TranslateM.runBackgroundChainIO js
        (Actor.response translator) dataMap ctx env
        callback chains prios
      IO.eprintln "Background process launched"
      IO.println (Json.mkObj [("status", "background"), ("token", toJson hash)])
    | some "lookup" =>
      IO.eprintln "Running in lookup mode"
      let .ok hash :=
        js.getObjValAs? UInt64 "token" | IO.throwServerError "No token provided"
      let result ← states.lookupJson hash
      putStrLn <| result.compress
    | some "quit" =>
      IO.eprintln "Exiting..."
      return 0
    | _ =>
      IO.eprintln "Running in foreground"
      let core := Actor.response translator js |>.runWithEmbeddings dataMap
      let result ←
        core.run' ctx {env := env} |>.runToIO'
      IO.eprintln "Ran successfully"
      putStrLn <| result.compress
      IO.eprintln "Output sent."
    process_loop env getLine putStrLn translator dataMap states chains

unsafe def launchProcess (p : Parsed) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let translator : Translator ←  Translator.ofCli p
  -- IO.eprintln <| toJson translator
  let env ←
    importModules (loadExts := true) #[{module := `Mathlib},
    {module:= `LeanAide.TheoremElab},
    {module:= `LeanCodePrompts.Translate},
    {module:= `LeanAide.StructToLean},
    {module:= `LeanAide.PaperCodes},
    {module:= `LeanAide.Responses},
    {module := `LeanAideCore}] {}
  withUnpickle (← picklePath "docString")
    <|fun (docStringData : EmbedData) => do
  withUnpickle (← picklePath "description")
    <|fun (descData : EmbedData) =>  do
  withUnpickle (← picklePath "concise-description")
    <|fun (concDescData : EmbedData) => do
  let dataMap :
    EmbedMap := Std.HashMap.ofList [("docString", docStringData), ("description", descData), ("concise-description", concDescData)]
  let stdin ←  IO.getStdin
  let stdout ← IO.getStdout
  let getLine : IO String := stdin.getLine
  let putStrLn : String → IO Unit := fun s => do
    stdout.putStrLn s
    stdout.flush
  let states : TasksState ←
    Std.Mutex.new <| Std.HashMap.emptyWithCapacity 100
  process_loop env getLine putStrLn translator dataMap states (fun _ _ => #[])


unsafe def leanAideProcess : Cmd := `[Cli|
  leanaide_process VIA launchProcess;
  "Elaborate a set of inputs and report whether successful and the result if successful."

  FLAGS:
    include_fixed;         "Include the 'Lean Chat' fixed prompts."
    p, prompts : Nat;      "Number of example prompts (default 20)."
    descriptions : Nat; "Number of example descriptions (default 2)."
    concise_descriptions : Nat; "Number of example concise descriptions (default 2)."
    leansearch_prompts: Nat; "Number of examples from LeanSearch"
    moogle_prompts: Nat; "Number of examples from Moogle"
    n, num_responses : Nat;    "Number of responses to ask for (default 10)."
    t, temperature : Nat;  "Scaled temperature `t*10` for temperature `t` (default 8)."
    m, model : String ; "Model to be used (default `gpt-4o`)"
    azure; "Use Azure instead of OpenAI."
    gemini; "Use Gemini with OpenAI API."
    url : String; "URL to query (for a local server)."
    examples_url : String; "URL to query for nearby embeddings (for a generic server)."
    auth_key : String; "Authentication key (for a local or generic server)."
    show_prompt; "Output the prompt to the LLM."
    show_elaborated; "Output the elaborated terms"
    max_tokens : Nat; "Maximum tokens to use in the translation."
    no_sysprompt; "The model has no system prompt (not relevant for GPT models)."

]

unsafe def main (args: List String) : IO UInt32 :=
  leanAideProcess.validate args
