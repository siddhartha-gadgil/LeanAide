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

def runTranslate (p : Parsed) : IO UInt32 := do
  initSearchPath (← findSysroot)
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
    |>.getD "gpt-5"
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
  -- withUnpickle (← picklePath "docString")
  --   <|fun (docStringData : EmbedData) => do
  -- withUnpickle (← picklePath "description")
  --   <|fun (descData : EmbedData) =>  do
  -- withUnpickle (← picklePath "concise-description")
  --   <|fun (concDescData : EmbedData) => do
  -- let dataMap :
  --   EmbedMap := Std.HashMap.ofList [("docString", docStringData), ("description", descData), ("concise-description", concDescData)]
  let names := p.variableArgsAs! String
  -- let name :=
  --   p.positionalArg? "input" |>.map (fun s => s.as! String)
  --   |>.get!
  let mut matched := 0
  let mut mismatched := 0
  for name in names do
    let name := name.toName
    logToStdErr `leanaide.translate.info s!"Translating {name}"
    let translator : Translator := {server := chatServer, params := {chatParams with n := 1}}
    let coreDesc := translator.getDescriptionCore name
    let io? :=
      coreDesc.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 0, maxRecDepth := 1000000}
      {env := env}
    let io?' ← io?.toIO'
    match io?' with
    | .error e => do
      let msg ← e.toMessageData.toString
      logToStdErr `leanaide.translate.info "Could not get description"
      logToStdErr `leanaide.translate.info msg
    | .ok none => do
      logToStdErr `leanaide.translate.info "No description"
    | Except.ok <| some (statement, desc) =>
      logToStdErr `leanaide.translate.info "Got description"
      logToStdErr `leanaide.translate.info statement
      logToStdErr `leanaide.translate.info desc
      let translator' := {translator with pb :=  (PromptExampleBuilder.embedBuilder numSim numConcise numDesc)}
      let coreTranslate :=
        translator'.translateViewVerboseM desc  |>.runToCore
      let io? :=
        coreTranslate.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 0, maxRecDepth := 1000000}
        {env := env}
      let io?' ← io?.toIO'
      match io?' with
      | Except.ok (translation?, output, prompt) =>
        logToStdErr `leanaide.translate.info "Ran successfully"
        if showPrompt then
          logToStdErr `leanaide.translate.info "Prompt:"
          logToStdErr `leanaide.translate.info prompt.pretty
          logToStdErr `leanaide.translate.info "---"
        match translation? with
        | some res =>
          if p.hasFlag "show_elaborated" then
            logToStdErr `leanaide.translate.info "Elaborated terms:"
            for out in res.allElaborated do
              logToStdErr `leanaide.translate.info out
            logToStdErr `leanaide.translate.info "---"
            logToStdErr `leanaide.translate.info "Groups:"
            for gp in res.groups do
              for out in gp do
                logToStdErr `leanaide.translate.info out
              logToStdErr `leanaide.translate.info "---"
          logToStdErr `leanaide.translate.info "Translation:"
          IO.println res.view
          let coreCompare := compareThmNameExprCore name res.term
          let io? :=
            coreCompare.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 0, maxRecDepth := 1000000}
            {env := env}
          let io?' ← io?.toIO'
          match io?' with
          | Except.ok b =>
            logToStdErr `leanaide.translate.info "Compared successfully"
            IO.println s!"Roundtrip match : {b}"
            if b then matched := matched + 1
            else mismatched := mismatched + 1
          | Except.error e =>
            logToStdErr `leanaide.translate.info "Could not compare"
            let msg ← e.toMessageData.toString
            logToStdErr `leanaide.translate.info msg
        | none =>
          logToStdErr `leanaide.translate.info "No translation"
          logToStdErr `leanaide.translate.info "All outputs:"
          for out in output do
            logToStdErr `leanaide.translate.info <| "* " ++ out
      | Except.error e =>
        do
          logToStdErr `leanaide.translate.info "Ran with error"
          let msg ← e.toMessageData.toString
          logToStdErr `leanaide.translate.info msg
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
    m, model : String ; "Model to be used (default `gpt-5.1`)"
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
