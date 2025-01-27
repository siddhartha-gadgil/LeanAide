import Lean.Meta
import LeanCodePrompts
import LeanCodePrompts.BatchTranslate
import LeanAide.Config
import LeanAide.TranslateM
import LeanAide.PromptBuilder
import LeanAide.TranslatorParams
import Cli
open Lean Cli LeanAide.Meta LeanAide Translator Translate

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def runTranslate (p : Parsed) : IO UInt32 := do
  searchPathRef.set compile_time_search_path%
  let type :=
    p.positionalArg? "input" |>.map (fun s => s.as! String)
    |>.getD "thm"
  let translator := Translator.ofCli p
  let model := translator.server.model
  let showPrompt := p.hasFlag "show_prompt"
  let tag := p.hasFlag "tag"
  let gitHash ← gitHash
  let dir :=
    if tag then System.mkFilePath <| ["results", model, gitHash]
    else System.mkFilePath <| ["results", model]
  if !(← dir.pathExists) then
        IO.FS.createDirAll dir
  let env ←
    importModules #[{module := `Mathlib},
    {module:= `LeanAide.TheoremElab},
    {module:= `LeanCodePrompts.Translate}] {}
  let core :=
    translator.translateViewVerboseM type   |>.runToCore
  let io? :=
    core.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 0, maxRecDepth := 1000000}
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
    | some result =>
      IO.eprintln "Translation:"
      IO.println result.view
      if p.hasFlag "roundtrip" then
        IO.eprintln "Roundtrip:"
        let core :=
          translator.checkTranslationM result.view result.term |>.run' {}
          let io? :=
            core.run' {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 0, maxRecDepth := 1000000}
            {env := env}
          let io?' ← io?.toIO'
          match io?' with
          | Except.ok <| some p =>
            let trans:= p.1
            let checks := p.2
            IO.eprintln "Checked translation"
            IO.eprintln "Translation:"
            IO.eprintln trans
            IO.eprintln "Checks:"
            for check in checks do
              IO.eprintln check
          | Except.ok none =>
            IO.eprintln "Ran with error (no output)"
            return 1
          | Except.error e =>
            do
              IO.eprintln "Ran with error"
              let msg ← e.toMessageData.toString
              IO.eprintln msg
      if p.hasFlag "show_elaborated" then
        IO.eprintln "Elaborated terms:"
        for out in result.allElaborated do
          IO.eprintln out
        IO.eprintln "---"
        IO.eprintln "Groups:"
        for gp in result.groups do
          for out in gp do
            IO.eprintln out
          IO.eprintln "---"
      return 0
    | none =>
      IO.eprintln "No translation"
      IO.eprintln "All outputs:"
      for out in output do
        IO.eprintln <| "* " ++ out
      return 2
  | Except.error e =>
    do
      IO.eprintln "Ran with error"
      let msg ← e.toMessageData.toString
      IO.eprintln msg
      return 1


def translateCmd : Cmd := `[Cli|
  translate VIA runTranslate;
  "Elaborate a set of inputs and report whether successful and the result if successful."

  FLAGS:
    include_fixed;         "Include the 'Lean Chat' fixed prompts."
    prompt_examples : String; "Example prompts in Json"
    p, prompts : Nat;      "Number of example prompts (default 10)."
    concise_descriptions : Nat; "Number of example concise descriptions (default 2)."
    descriptions : Nat; "Number of example descriptions (default 2)."
    r, responses : Nat;    "Number of responses to ask for (default 10)."
    t, temperature : Nat;  "Scaled temperature `t*10` for temperature `t` (default 8)."
    m, model : String ; "Model to be used (default `gpt-4o`)"
    roundtrip; "Roundtrip the translation."
    azure; "Use Azure instead of OpenAI."
    gemini; "Use Gemini instead of OpenAI."
    url : String; "URL to query (for a local or generic server)."
    auth_key : String; "Authentication key (for a local or generic server)."
    show_prompt; "Output the prompt to the LLM."
    show_elaborated; "Output the elaborated terms"
    max_tokens : Nat; "Maximum tokens to use in the translation."
    no_sysprompt; "The model has no system prompt (not relevant for GPT models)."

  ARGS:
    input : String;      "The input file in the `data` folder."

]

def main (args: List String) : IO UInt32 :=
  translateCmd.validate args
