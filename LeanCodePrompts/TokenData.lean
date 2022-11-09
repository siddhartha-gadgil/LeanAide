import LeanCodePrompts.CheckParse
import Mathbin.All
open Lean

syntax  " ∥ " term " ∥ " : term

def thmsForTokens := IO.FS.lines "data/parsed_thms.txt"

def thmTokens : MetaM (Array (String × Array String)) := do
    let lines ← thmsForTokens
    let thmTokens ←  lines.mapM <| fun s => do pure (s, ← getTokens s)
    return thmTokens


def writeTokens : MetaM Unit := do
  let thmTokens ← thmTokens
  let lines := thmTokens.map <| 
    fun (thm, tokens) => tokens.foldl 
      (fun acc token => acc ++ ", " ++ token.quote) thm.quote
  let text := lines.foldl (fun acc line => acc ++ line ++ "\n") ""
  IO.FS.writeFile "data/parsed_thms_tokens.txt" text
#eval thmTokens

-- #check String.quote

-- #eval writeTokens

