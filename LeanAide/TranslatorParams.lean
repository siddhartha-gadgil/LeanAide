import LeanAide.PromptBuilder
import Cli

namespace LeanAide

open Cli Translator Lean

def Translator.ofCli (p: Parsed) : Translator :=
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
  let embedUrl? := p.flag? "embed_url" |>.map (fun s => s.as! String)
  let pb := match pb? with
    | some pb => pb
    | none =>
      let pb₁ := pb?.getD <|
        PromptExampleBuilder.mkEmbedBuilder embedUrl? numSim numConcise numDesc
      let pb₂ := PromptExampleBuilder.searchBuilder numLeanSeach numMoogle |>.simplify
      if numLeanSeach + numMoogle > 0 then
        pb₁ ++ pb₂
      else pb₁
  let pb := pb.simplify
  let queryNum := p.flag? "num_responses" |>.map (fun s => s.as! Nat)
    |>.getD 10
  let temp10 := p.flag? "temperature" |>.map (fun s => s.as! Nat)
    |>.getD 8
  let temp : JsonNumber := ⟨temp10, 1⟩
  let gemini := p.hasFlag "gemini"
  let model := p.flag? "model" |>.map (fun s => s.as! String)
    |>.getD (if gemini then "gemini-1.5-pro-001" else "gpt-4o")
  let azure := p.hasFlag "azure"
  let maxTokens := p.flag? "max_tokens" |>.map (fun s => s.as! Nat)
    |>.getD 1600
  let sysLess := p.hasFlag "no_sysprompt"
  let url? := p.flag? "url" |>.map (fun s => s.as! String)
  let authKey? := p.flag? "auth_key" |>.map (fun s => s.as! String)
  let chatServer :=
    if azure then ChatServer.azure else
    if gemini then ChatServer.google model else
        match url? with
        | some url => ChatServer.generic model url none !sysLess
        | none => ChatServer.openAI model
  let chatServer := chatServer.addKeyOpt authKey?
  let chatParams : ChatParams :=
    {temp := temp, n := queryNum, maxTokens := maxTokens}
  let translator : Translator := {pb := pb, server := chatServer, params := chatParams}
  translator

end LeanAide

open Lean
structure Eg where
  x : Nat
  y? : Option Nat
deriving ToJson, FromJson, Repr

#eval fromJson? (α := Eg) (toJson ({ x := 1, y? := none } : Eg))

#eval fromJson? (α := Eg) (Json.mkObj [("x", toJson 1), ("extra", 7)])
