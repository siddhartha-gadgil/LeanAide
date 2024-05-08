import Lean.Meta
import LeanCodePrompts
import LeanCodePrompts.BatchTranslate
import LeanAide.Config
import Cli
open Lean Cli

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def runBulkElab (p : Parsed) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  let type :=
    p.positionalArg? "input" |>.map (fun s => s.as! String)
    |>.getD "thm"
  let numSim := p.flag? "prompts" |>.map (fun s => s.as! Nat)
    |>.getD 10
  let numConcise := p.flag? "concise_descriptions" |>.map
    (fun s => s.as! Nat) |>.getD 2
  let includeFixed := p.hasFlag "include_fixed"
  let queryNum := p.flag? "responses" |>.map (fun s => s.as! Nat)
    |>.getD 5
  let temp10 := p.flag? "temperature" |>.map (fun s => s.as! Nat)
    |>.getD 8
  let temp : JsonNumber := ⟨temp10, 1⟩
  let model := p.flag? "model" |>.map (fun s => s.as! String)
    |>.getD "gpt-3.5-turbo"
  let embedding := p.flag? "embedding" |>.map (fun s => s.as! String)
    |>.getD "openai_full"
  let delay := p.flag? "delay" |>.map (fun s => s.as! Nat)
    |>.getD 20
  let repeats := p.flag? "repeats" |>.map (fun s => s.as! Nat)
    |>.getD 0
  let maxTokens := p.flag? "max_tokens" |>.map (fun s => s.as! Nat)
    |>.getD 1600
  let azure := p.hasFlag "azure"
  let tag := p.hasFlag "tag"
  let url? := p.flag? "url" |>.map (fun s => s.as! String)
  let sysLess := p.hasFlag "no_sysprompt"
  let chatServer :=
    if azure then ChatServer.azure (model := model) else
        match url? with
        | some url => ChatServer.generic model url !sysLess
        | none => ChatServer.openAI model
  let chatParams : ChatParams :=
    let params: ChatParams :=
      {temp := temp, n := queryNum, maxTokens := maxTokens}
    params.withoutStop (p.hasFlag "no_stop")
  let queryData? : Option (HashMap String Json) ←
    p.flag? "query_data" |>.map (fun s => s.as! String) |>.mapM
      fun filename => do
        let lines ←  IO.FS.lines filename
        let mut qdMap := HashMap.empty
        for l in lines do
          let json? := Json.parse l
          match json? with
          | Except.ok json =>
            let doc := (json.getObjValAs? String "docString" |>.toOption.orElse
            (fun _ => json.getObjValAs? String "doc_string" |>.toOption)
            ).get!
            let out := json.getObjValAs? Json "choices" |>.toOption.get!
            qdMap := qdMap.insert doc out
            IO.println doc
          | Except.error e => do
            throw <| IO.userError s!"Error parsing query data file: {e}"

        pure qdMap
  let gitHash ← gitHash
  let dir :=
    if tag then System.mkFilePath <| ["results", model, gitHash]
    else System.mkFilePath <| ["results", model]
  if !(← dir.pathExists) then
        IO.FS.createDirAll dir
  let outFile :=
    if tag then
        System.mkFilePath <|
    p.flag? "output" |>.map (fun s => [s.as! String]) |>.getD
      ["results", model, gitHash, s!"{type}-elab-{numSim}-{includeFixed}-{queryNum}-{temp10}.json"]
    else
    System.mkFilePath <|
    p.flag? "output" |>.map (fun s => [s.as! String]) |>.getD
      ["results", model, s!"{type}-elab-{numSim}-{includeFixed}-{queryNum}-{temp10}.json"]
  let env ←
    importModules #[{module := `Mathlib},
    {module:= `LeanAide.TheoremElab},
    {module:= `LeanCodePrompts.Translate},
    {module := `Mathlib}] {}
  let core :=
    checkTranslatedThmsCore type chatServer chatParams numSim numConcise includeFixed embedding delay repeats queryData? tag
  let io? :=
    core.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 100000000000, maxRecDepth := 1000000}
    {env := env}
  match ← io?.toIO' with
  | Except.ok js =>
    IO.println "Success"
    IO.FS.writeFile outFile js.pretty
    -- IO.println js.pretty
    IO.println s!"Written to file {outFile}"
  | Except.error e =>
    do
          IO.println "Ran with error"
          let msg ← e.toMessageData.toString
          IO.println msg

  return 0

def bulkElab : Cmd := `[Cli|
  bulkelab VIA runBulkElab;
  "Elaborate a set of inputs and report whether successful and the result if successful."

  FLAGS:
    include_fixed;         "Include the 'Lean Chat' fixed prompts."
    o, output : String;    "Output file (default `results/{type}-elab-{numSim}-{includeFixed}-{queryNum}-{temp10}.json`)."
    p, prompts : Nat;      "Number of example prompts (default 10)."
    concise_descriptions : Nat; "Number of example descriptions (default 2)."
    r, responses : Nat;    "Number of responses to ask for (default 5)."
    t, temperature : Nat;  "Scaled temperature `t*10` for temperature `t` (default 8)."
    m, model : String ; "Model to be used (default `gpt-3.5-turbo`)"
    e, embedding : String; "Embedding to be used (default `openai_full`)"
    d, delay : Nat; "Delay between requests in seconds (default 20)."
    query_data : String; "Query data jsonlines file if cached queries are to be used; should have the result of the 'choices' field of the output and a 'docString' field for the query."
    repeats : Nat; "Number of times to repeat the request (default 0)."
    azure; "Use Azure instead of OpenAI."
    url : String; "URL to query (for a local server)."
    tag; "Include the git hash in the results filepath"
    no_stop; "Don't use `:=` as a stop token."
    max_tokens : Nat; "Maximum tokens to use in the translation."
    no_sysprompt; "The model has no system prompt (not relevant for GPT models)."

  ARGS:
    input : String;      "The input file in the `data` folder."

]

def main (args: List String) : IO UInt32 :=
  bulkElab.validate args
