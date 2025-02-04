import Lean.Meta
import LeanCodePrompts
import LeanCodePrompts.BatchTranslate
import LeanAide.Config
import LeanAide.TranslatorParams
import Cli
open Lean Cli LeanAide.Meta LeanAide Translator Translate

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

unsafe def runBulkElab (p : Parsed) : IO UInt32 := do
  initSearchPath (← Lean.findSysroot) initFiles
  let input_file :=
    p.positionalArg? "input" |>.map (fun s => s.as! String)
    |>.getD "thm"
  let numSim := p.flag? "prompts" |>.map (fun s => s.as! Nat)
    |>.getD 10
  let numConcise := p.flag? "concise_descriptions" |>.map
    (fun s => s.as! Nat) |>.getD 2
  let numDesc := p.flag? "descriptions" |>.map
    (fun s => s.as! Nat) |>.getD 2
  let pb₁ :=
    PromptExampleBuilder.embedBuilder numSim numConcise numDesc |>.simplify
  let numLeanSeach := p.flag? "leansearch_prompts" |>.map
    (fun s => s.as! Nat) |>.getD 0
  let numMoogle := p.flag? "moogle_prompts" |>.map
    (fun s => s.as! Nat) |>.getD 2
  let pb₂ := PromptExampleBuilder.searchBuilder numLeanSeach numMoogle |>.simplify
  let includeFixed := p.hasFlag "include_fixed"
  let pb :=
    if includeFixed then pb₁ ++ pb₂ ++ PromptExampleBuilder.proofNetPromptBuilder
    else pb₁ ++ pb₂
  let queryNum := p.flag? "num_responses" |>.map (fun s => s.as! Nat)
    |>.getD 5
  let temp10 := p.flag? "temperature" |>.map (fun s => s.as! Nat)
    |>.getD 8
  let temp : JsonNumber := ⟨temp10, 1⟩
  let model := p.flag? "model" |>.map (fun s => s.as! String)
    |>.getD "gpt-4o"
  let maxTokens := p.flag? "max_tokens" |>.map (fun s => s.as! Nat)
    |>.getD 1600
  let chatParams : ChatParams :=
    let params: ChatParams :=
      {temp := temp, n := queryNum, maxTokens := maxTokens}
    params.withoutStop (p.hasFlag "no_stop")
  let translator : Translator := Translator.ofCli p
  let tag := p.hasFlag "tag"
  let delay := p.flag? "delay" |>.map (fun s => s.as! Nat)
    |>.getD 20
  let repeats := p.flag? "repeats" |>.map (fun s => s.as! Nat)
    |>.getD 0
  let queryData? : Option (Std.HashMap String Json) ←
    p.flag? "query_data" |>.map (fun s => s.as! String) |>.mapM
      fun filename => do
        let lines ←  IO.FS.lines filename
        let mut qdMap := Std.HashMap.empty
        for l in lines do
          let json? := Json.parse l
          match json? with
          | Except.ok json =>
            let doc := (json.getObjValAs? String "docString" |>.toOption.orElse
            (fun _ => json.getObjValAs? String "doc_string" |>.toOption)
            ).get!
            let out := json.getObjVal? "choices" |>.toOption.get!
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
      ["results", model, gitHash, s!"{input_file}-elab-{pb.signature}-{chatParams.n}-{chatParams.temp.mantissa}.json"]
    else
    System.mkFilePath <|
    p.flag? "output" |>.map (fun s => [s.as! String]) |>.getD
      ["results", model, s!"{input_file}-elab-{pb.signature}-{chatParams.n}-{chatParams.temp.mantissa}.json"]
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
  IO.eprintln "Loading hashmap"
  let dataMap :
    EmbedMap := Std.HashMap.ofList [("docString", docStringData), ("description", descData), ("concise-description", concDescData)]
  IO.eprintln "Loaded hashmap"
  let core :=
    translator.checkTranslatedThmsM input_file  delay repeats
    queryData? tag |>.runWithEmbeddings dataMap
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

unsafe def bulkElab : Cmd := `[Cli|
  bulkelab VIA runBulkElab;
  "Elaborate a set of inputs and report whether successful and the result if successful."

  FLAGS:
    include_fixed;         "Include the 'Lean Chat' fixed prompts."
    o, output : String;    "Output file (default `results/{type}-elab-{numSim}-{queryNum}-{temp10}.json`)."
    roundtrip; "Translate back to natural language and compare."
    prompt_examples : String; "Example prompts in Json"
    p, prompts : Nat;      "Number of example prompts (default 10)."
    concise_descriptions : Nat; "Number of example concise descriptions (default 2)."
    descriptions : Nat; "Number of example descriptions (default 2)."
    leansearch_prompts: Nat; "Number of examples from LeanSearch"
    moogle_prompts: Nat; "Number of examples from Moogle"
    n, num_responses : Nat;    "Number of responses to ask for (default 5)."
    t, temperature : Nat;  "Scaled temperature `t*10` for temperature `t` (default 8)."
    roundtrip; "Translate back to natural language and compare."
    m, model : String ; "Model to be used (default `gpt-4o`)"
    d, delay : Nat; "Delay between requests in seconds (default 20)."
    query_data : String; "Query data jsonlines file if cached queries are to be used; should have the result of the 'choices' field of the output and a 'docString' field for the query."
    repeats : Nat; "Number of times to repeat the request (default 0)."
    azure; "Use Azure instead of OpenAI."
    url : String; "URL to query (for a local server)."
    examples_url : String; "URL to query for nearby embeddings (for a generic server)."
    tag; "Include the git hash in the results filepath"
    no_stop; "Don't use `:=` as a stop token."
    max_tokens : Nat; "Maximum tokens to use in the translation."
    no_sysprompt; "The model has no system prompt (not relevant for GPT models)."

  ARGS:
    input : String;      "The input file in the `data` folder."

]

unsafe def main (args: List String) : IO UInt32 :=
  bulkElab.validate args
