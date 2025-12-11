import LeanAide.PromptBuilder
-- import LeanAide.TomlConfig
import Cli

namespace LeanAide

open Cli Translator Lean

#check Parsed.variableArgs

def Translator.ofCli (p: Parsed) : IO Translator :=
  let numSim := p.flag? "prompts" |>.map (fun s => s.as! Nat)
    |>.getD 20
  let numConcise := p.flag? "concise_descriptions" |>.map (fun s => s.as! Nat)
    |>.getD 2
  let numDesc := p.flag? "descriptions" |>.map
    (fun s => s.as! Nat) |>.getD 2
  let pbSource? := p.flag? "prompt_examples" |>.map
    (fun s => s.as! String)
  let pbJs? := pbSource?.bind fun pb =>
    (Json.parse pb |>.toOption)
  let pb? : Option PromptExampleBuilder := pbJs?.bind
    fun js =>
      fromJson? js |>.toOption
  let numLeanSeach := p.flag? "leansearch_prompts" |>.map
    (fun s => s.as! Nat) |>.getD 0
  let numMoogle := p.flag? "moogle_prompts" |>.map
    (fun s => s.as! Nat) |>.getD 0
  let embedUrl? := p.flag? "examples_url" |>.map (fun s => s.as! String)
  let pb := match pb? with
    | some pb => pb
    | none =>
      let pb₁ :=
        PromptExampleBuilder.mkSimilarBuilder embedUrl? numSim numConcise numDesc
      let pb₂ := PromptExampleBuilder.searchBuilder numLeanSeach numMoogle |>.simplify
      if numLeanSeach + numMoogle > 0 then
        pb₁ ++ pb₂
      else pb₁
  let pb := pb.simplify
  let queryNum := p.flag? "num_responses" |>.map (fun s => s.as! Nat)
    |>.getD 8
  let temp10 := p.flag? "temperature" |>.map (fun s => s.as! Nat)
    |>.getD 10
  let temp : JsonNumber := ⟨temp10, 1⟩
  let gemini := p.hasFlag "gemini"
  let model := p.flag? "model" |>.map (fun s => s.as! String)
    |>.getD (if gemini then "gemini-2.0-flash" else "gpt-5")
  let azure := p.hasFlag "azure"
  let maxTokens := p.flag? "max_tokens" |>.map (fun s => s.as! Nat)
    |>.getD 1600
  let sysLess := p.hasFlag "no_sysprompt"
  let url? := p.flag? "url" |>.map (fun s => s.as! String)
  let authKey? := p.flag? "auth_key" |>.map (fun s => s.as! String)
  let chatServer :=
    if azure then ChatServer.azure else
    if gemini then .gemini model else
        match url? with
        | some url =>
          ChatServer.generic model url none !sysLess
        | none => ChatServer.openAI model
  let chatServer := chatServer.addKeyOpt authKey?
  let chatParams : ChatParams :=
    {temp := temp, n := queryNum, maxTokens := maxTokens}
  let translator : Translator := {pb := pb, server := chatServer, params := chatParams}
  return translator

def Translator.patch (translator: Translator) (data: Json) : Translator :=
  match data.getObjVal? "translator" with
  | Except.ok config =>
    let json := (toJson translator).mergeObj config
    fromJson? (α := Translator) json |>.toOption.getD translator
  | _ => translator

def Translator.CliDefaultJson := json% {"useInstructions": true,
 "toChat": "simple",
 "server": {"openAI": {"model": "gpt-4o", "authHeader?": null}},
 "roundTripSelect": false,
 "roundTrip": false,
 "relDefs": {"seq": []},
 "reasoningServer": {"openAI": {"model": "o3-mini", "authHeader?": null}},
 "pb":
 {"blend":
  [{"similarSearch": {"n": 20, "descField": "docString"}},
   {"similarSearch": {"n": 2, "descField": "concise-description"}},
   {"similarSearch": {"n": 2, "descField": "description"}}]},
 "params": {"temp": 1, "stopTokens": [], "n": 10, "maxTokens": 1600},
 "messageBuilder": {"directBuilder":
  {"userHead": "user",
  "headMessage":
  "You are a coding assistant who translates from natural language to Lean Theorem Prover code following examples. The translated code is preceded by `import Mathlib._`, so do not include import statements. Suppress proofs for brevity. Follow EXACTLY the examples given.",
  "egsHead":
  "The following are some examples of statements and their translations (proofs are suppressed for brevity):",
  "egResponseHead": "## Lean Code\
\
",
  "egQueryHead": "## Natural language statement\
\
"}}}

@[deprecated Translator.patch (since := "2025-11-04")]
def Translator.configure (translator: Translator) (config: Json) : Translator :=
  let n := config.getObjValAs? Nat "n" |>.toOption.getD translator.params.n
  let translator := {translator with params := {translator.params with n := n}}
  let temp? :=
    config.getObjValAs? JsonNumber "temperature" |>.toOption
  let temp := temp? |>.getD translator.params.temp
  let translator := {translator with params := {translator.params with temp := temp}}
  let maxTokens := config.getObjValAs? Nat "max_tokens" |>.toOption
    |>.getD translator.params.maxTokens
  let translator := {translator with params := {translator.params with maxTokens := maxTokens}}
  let server := match config.getObjVal?  "server" with
    | Except.ok server =>
        let model := server.getObjValAs? String "model" |>.toOption
          |>.getD translator.server.model
        let url? := server.getObjValAs? String "url" |>.toOption
        let gemini := server.getObjValAs? Bool "gemini" |>.toOption
          |>.getD (model.startsWith "gemini")
        let azure := server.getObjValAs? Bool "azure" |>.toOption
          |>.getD false
        let sysLess := server.getObjValAs? Bool "no_sysprompt" |>.toOption
          |>.getD false
        if azure then ChatServer.azure else
        if gemini then .gemini model else
            match url? with
            | some url => ChatServer.generic model url none !sysLess
            | none => ChatServer.openAI model
    | _ => translator.server
  let authKey? :=
    config.getObjValAs? String "auth_key" |>.toOption
  let chatServer := server.addKeyOpt authKey?
  let translator := {translator with server := chatServer}
  let translator := match config.getObjValAs? Bool "reasoning" with
    | Except.ok true => translator.reasoning
    | _ => translator
  let translator := match config.getObjVal? "examples" with
    | Except.ok js =>
      let numSim := js.getObjValAs? Nat "docstrings" |>.toOption.getD 20
      let numConcise := js.getObjValAs? Nat "concise_descriptions"
        |>.toOption.getD 2
      let numDesc := js.getObjValAs? Nat "descriptions"
        |>.toOption.getD 2
      let embedUrl? := js.getObjValAs? String "examples_url" |>.toOption
      let pb₁ := PromptExampleBuilder.mkSimilarBuilder embedUrl? numSim numConcise numDesc
      let pb₂ := PromptExampleBuilder.searchBuilder 0 0 |>.simplify
      let pb := pb₁ ++ pb₂
      let pb := pb.simplify
      {translator with pb := pb}
    | _ => translator
  translator

end LeanAide

open Lean
structure Eg where
  x : Nat
  y? : Option Nat
deriving ToJson, FromJson, Repr

-- #eval fromJson? (α := Eg) (toJson ({ x := 1, y? := none } : Eg))

-- #eval fromJson? (α := Eg) (Json.mkObj [("x", toJson 1), ("extra", 7)])
