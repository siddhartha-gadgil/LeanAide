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
  initSearchPath (← Lean.findSysroot) initFiles
  let type := 
    p.positionalArg? "input" |>.map (fun s => s.as! String)
    |>.getD "thm"
  let numSim := p.flag? "prompts" |>.map (fun s => s.as! Nat)
    |>.getD 10
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
  let azure := p.hasFlag "azure"
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

  let outFile := System.mkFilePath 
      ["results", 
      s!"{type}-elab-{numSim}-{includeFixed}-{queryNum}-{temp10}.json"]
  let env ← 
    importModules [{module := `Mathlib},
    {module:= `LeanAide.TheoremElab},
    {module:= `LeanCodePrompts.Translate},    
    {module := `Mathlib}] {}
  let core := 
    checkTranslatedThmsCore type
      numSim includeFixed queryNum temp model embedding azure 
      delay repeats queryData?
  let io? := 
    core.run' {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000} 
    {env := env}
  match ← io?.toIO' with
  | Except.ok js =>
    IO.println "Success"
    IO.FS.writeFile outFile js.pretty
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
    p, prompts : Nat;      "Number of example prompts (default 10)."
    r, responses : Nat;    "Number of responses to ask for (default 5)."
    t, temperature : Nat;  "Scaled temperature `t*10` for temperature `t`."
    m, model : String ; "Model to be used (default `gpt-3.5-turbo`)"
    e, embedding : String; "Embedding to be used (default `openai_full`)"
    d, delay : Nat; "Delay between requests in seconds (default 20)."
    query_data : String; "Query data jsonlines file if cached queries are to be used; should have the result of the 'choices' field of the output and a 'docString' field for the query."
    repeats : Nat; "Number of times to repeat the request (default 0)."
    azure; "Use Azure instead of OpenAI."

  ARGS:
    input : String;      "The input file in the `data` folder."

]

def main (args: List String) : IO UInt32 := 
  bulkElab.validate args