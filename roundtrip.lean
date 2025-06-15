import Lean.Meta
import LeanCodePrompts
import LeanCodePrompts.BatchTranslate
import LeanAide.Config
import LeanAide.Descriptions
import Cli
open Lean Cli LeanAide.Meta LeanAide

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

unsafe def runTranslate (p : Parsed) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  let numSim := p.flag? "prompts" |>.map (fun s => s.as! Nat)
    |>.getD 20
  let numConcise := p.flag? "concise_descriptions" |>.map (fun s => s.as! Nat)
    |>.getD 2
  let numDesc := p.flag? "descriptions" |>.map (fun s => s.as! Nat)
    |>.getD 2

  let queryNum := p.flag? "num_responses" |>.map (fun s => s.as! Nat)
    |>.getD 10
  let temp10 := p.flag? "temperature" |>.map (fun s => s.as! Nat)
    |>.getD 8
  let temp : JsonNumber := ⟨temp10, 1⟩
  let model := p.flag? "model" |>.map (fun s => s.as! String)
    |>.getD "gpt-4o"
  let azure := p.hasFlag "azure"
  let tag := p.hasFlag "tag"
  let maxTokens := p.flag? "max_tokens" |>.map (fun s => s.as! Nat)
    |>.getD 1600
  let sysLess := p.hasFlag "no_sysprompt"
  let url? := p.flag? "url" |>.map (fun s => s.as! String)
  let showPrompt := p.hasFlag "show_prompt"
  let chatServer :=
    if azure then ChatServer.azure else
        match url? with
        | some url => ChatServer.generic model url none !sysLess
        | none => ChatServer.openAI model
  let chatParams : ChatParams :=
    {temp := temp, n := queryNum, maxTokens := maxTokens}
  let gitHash ← gitHash
  let dir :=
    if tag then System.mkFilePath <| ["results", model, gitHash]
    else System.mkFilePath <| ["results", model]
  if !(← dir.pathExists) then
        IO.FS.createDirAll dir
  let env ←
    importModules (loadExts := true) #[{module := `Mathlib},
    {module:= `LeanAide.TheoremElab},
    {module:= `LeanCodePrompts.Translate},
    {module:= `LeanAide.Descriptions}] {}
  withUnpickle (← picklePath "docString")
    <|fun (docStringData : EmbedData) => do
  withUnpickle (← picklePath "description")
    <|fun (descData : EmbedData) =>  do
  withUnpickle (← picklePath "concise-description")
    <|fun (concDescData : EmbedData) => do
  let dataMap :
    EmbedMap := Std.HashMap.ofList [("docString", docStringData), ("description", descData), ("concise-description", concDescData)]
  let names := p.variableArgsAs! String
  -- let name :=
  --   p.positionalArg? "input" |>.map (fun s => s.as! String)
  --   |>.get!
  let mut matched := 0
  let mut mismatched := 0
  for name in names do
    let name := name.toName
    IO.eprintln s!"Translating {name}"
    let translator : Translator := {server := chatServer, params := {chatParams with n := 1}}
    let coreDesc := translator.getDescriptionCore name
    let io? :=
      coreDesc.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 0, maxRecDepth := 1000000}
      {env := env}
    let io?' ← io?.toIO'
    match io?' with
    | .error e => do
      let msg ← e.toMessageData.toString
      IO.eprintln "Could not get description"
      IO.eprintln msg
    | .ok none => do
      IO.eprintln "No description"
    | Except.ok <| some (statement, desc) =>
      IO.eprintln "Got description"
      IO.eprintln statement
      IO.eprintln desc
      let translator' := {translator with pb :=  (PromptExampleBuilder.embedBuilder numSim numConcise numDesc)}
      let coreTranslate :=
        translator'.translateViewVerboseM desc  |>.runWithEmbeddings dataMap
      let io? :=
        coreTranslate.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 0, maxRecDepth := 1000000}
        {env := env}
      let io?' ← io?.toIO'
      match io?' with
      | Except.ok (translation?, output, prompt) =>
        IO.eprintln "Ran successfully"
        if showPrompt then
          IO.eprintln "Prompt:"
          IO.eprintln prompt.pretty
          IO.eprintln "---"
        match translation? with
        | some res =>
          if p.hasFlag "show_elaborated" then
            IO.eprintln "Elaborated terms:"
            for out in res.allElaborated do
              IO.eprintln out
            IO.eprintln "---"
            IO.eprintln "Groups:"
            for gp in res.groups do
              for out in gp do
                IO.eprintln out
              IO.eprintln "---"
          IO.eprintln "Translation:"
          IO.println res.view
          let coreCompare := compareThmNameExprCore name res.term
          let io? :=
            coreCompare.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 0, maxRecDepth := 1000000}
            {env := env}
          let io?' ← io?.toIO'
          match io?' with
          | Except.ok b =>
            IO.eprintln "Compared successfully"
            IO.println s!"Roundtrip match : {b}"
            if b then matched := matched + 1
            else mismatched := mismatched + 1
          | Except.error e =>
            IO.eprintln "Could not compare"
            let msg ← e.toMessageData.toString
            IO.eprintln msg
        | none =>
          IO.eprintln "No translation"
          IO.eprintln "All outputs:"
          for out in output do
            IO.eprintln <| "* " ++ out
      | Except.error e =>
        do
          IO.eprintln "Ran with error"
          let msg ← e.toMessageData.toString
          IO.eprintln msg
  IO.println s!"Matched: {matched}, Mismatched: {mismatched}"
  return 0

unsafe def roundtrip : Cmd := `[Cli|
  translate VIA runTranslate;
  "Elaborate a set of inputs and report whether successful and the result if successful."

  FLAGS:
    include_fixed;         "Include the 'Lean Chat' fixed prompts."
    p, prompts : Nat;      "Number of example prompts (default 20)."
    descriptions : Nat; "Number of example descriptions (default 2)."
    concise_descriptions : Nat; "Number of example concise descriptions (default 2)."
    n, num_responses : Nat;    "Number of responses to ask for (default 10)."
    t, temperature : Nat;  "Scaled temperature `t*10` for temperature `t` (default 8)."
    m, model : String ; "Model to be used (default `gpt-3.5-turbo`)"
    azure; "Use Azure instead of OpenAI."
    url : String; "URL to query (for a local server)."
    show_prompt; "Output the prompt to the LLM."
    show_elaborated; "Output the elaborated terms"
    max_tokens : Nat; "Maximum tokens to use in the translation."
    no_sysprompt; "The model has no system prompt (not relevant for GPT models)."

  ARGS:
    ...inputs : String;      "The name of the theorem to translate with a roundtrip."

]

unsafe def main (args: List String) : IO UInt32 :=
  roundtrip.validate args
