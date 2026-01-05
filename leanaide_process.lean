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

partial def process_loop (env: Environment)(getLine : IO String) (putStrLn : String → IO Unit)
    (translator : Translator)  (states : TasksState) (chains : Json → Json → Array (Json → TranslateM Json)) : IO UInt32 := do
  logToStdErr `leanaide.translate.info "Server ready. Waiting for input..."
  let inp ← getLine
  if inp.trim.isEmpty then
    process_loop env getLine putStrLn translator states chains
  else
  match Json.parse inp with
  | Except.error e =>
     logToStdErr `leanaide.translate.info s!"Error parsing input: {e}"
     process_loop env getLine putStrLn translator states chains
  | Except.ok js =>
    let mode? := js.getObjValAs? String "mode" |>.toOption
    let ctx: Core.Context := {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 0, maxRecDepth := 1000000}
    match mode? with
    | some "async" =>
      let hash := hash js
      let check? ← states.lookup hash
      match check? with
      | none =>
        logToStdErr `leanaide.translate.info "Running in background"
        states.addStart hash js
        let response_url? :=
          (js.getObjValAs? String "response_url").toOption
        let callback (js res : Json) : IO Unit := do
          logIO `leanaide.tasks.info s!"Background process completed for token: {hash}\ninput: {js.pretty}"
          logIO `leanaide.tasks.info s!"Output: {res.pretty}"
          let outfile : System.FilePath := ".leanaide_cache" / "tasks" / ("response_" ++ toString hash ++ ".json")
          IO.FS.writeFile outfile (res.pretty)
          match response_url? with
          | some url =>
            try
              let data :=
                Json.mkObj [("token", toJson hash), ("response", res)]
              let res ← IO.Process.run {cmd := "curl", args := #["-X", "POST", "-H", "Content-Type: application/json","--data", data.pretty, url]}
              logIO `leanaide.tasks.info s!"Posted results to {url} for token {hash}, response: {res}"
            catch e =>
              logIO `leanaide.tasks.warning s!"Failed to post results to {url} for token {hash}: {e}"
          | none => pure ()

          states.addResult hash res
        let prios :=
          (js.getObjValAs? Task.Priority "priority").toOption |>.getD Task.Priority.default
        TranslateM.runBackgroundChainIO js
          (Actor.response translator) none ctx env
          callback chains prios
        setLogProcess (s!"process:{hash}")
        logToStdErr `leanaide.translate.info "Background process launched"
        IO.println (Json.mkObj [("status", "background"), ("token", toJson hash)])
      | some ts =>
        IO.println (Json.mkObj [("status", (toJson ts).compress), ("token", toJson hash)]).compress
        logToStdErr `leanaide.translate.info s!"Task with token {hash} is already running, status: {(toJson ts).compress}."
    | some "lookup" =>
      logToStdErr `leanaide.translate.info "Running in lookup mode"
      let .ok hash :=
        js.getObjValAs? UInt64 "token" | IO.throwServerError "No token provided"
      let result ← states.lookupJson hash
      putStrLn <| result.compress
    | some "quit" =>
      logToStdErr `leanaide.translate.info "Exiting..."
      return 0
    | _ =>
      logToStdErr `leanaide.translate.info "Running in foreground"
      let core := Actor.response translator js |>.runToCore
      let result ←
        core.run' ctx {env := env} |>.runToIO'
      logToStdErr `leanaide.translate.info "Ran successfully"
      putStrLn <| result.compress
      logToStdErr `leanaide.translate.info "Output sent."
    process_loop env getLine putStrLn translator states chains

def launchProcess (p : Parsed) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let translator : Translator ←  Translator.ofCli p
  -- logToStdErr `leanaide.translate.info <| toJson translator
  let env ←
    importModules (loadExts := true) #[{module := `Mathlib},
    {module:= `LeanAide.TheoremElab},
    {module:= `LeanCodePrompts.Translate},
    {module:= `LeanAide.StructToLean},
    {module:= `LeanAide.PaperCodes},
    {module:= `LeanAide.Responses},
    {module := `LeanAideCore}] {}
  -- withUnpickle (← picklePath "docString")
  --   <|fun (docStringData : EmbedData) => do
  -- withUnpickle (← picklePath "description")
  --   <|fun (descData : EmbedData) =>  do
  -- withUnpickle (← picklePath "concise-description")
  --   <|fun (concDescData : EmbedData) => do
  -- let dataMap :
  --   EmbedMap := Std.HashMap.ofList [("docString", docStringData), ("description", descData), ("concise-description", concDescData)]
  let stdin ←  IO.getStdin
  let stdout ← IO.getStdout
  let getLine : IO String := stdin.getLine
  let putStrLn : String → IO Unit := fun s => do
    stdout.putStrLn s
    stdout.flush
  let states : TasksState ←
    Std.Mutex.new <| Std.HashMap.emptyWithCapacity 100
  process_loop env getLine putStrLn translator states (fun _ _ => #[])


def leanAideProcess : Cmd := `[Cli|
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
    m, model : String ; "Model to be used (default `gpt-5.1`)"
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
