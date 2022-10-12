import Lean
import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson
import LeanCodePrompts.ParseJson
import LeanCodePrompts.Utils

open Std Lean

initialize texCommandCache : IO.Ref (HashMap String String) ← do
  -- IO.println "Initialising TeX Command cache..."
  -- let js ← Json.parseFile "data/texcmds.json"
  -- let l := js.map $ fun j => (j[0]!.getStr!, j[1]!.getStr!)
  let .obj js ← IO.ofExcept $ Json.parse $ ← IO.FS.readFile "data/full-tex.json" | panic! "Invalid JSON format"
  let l : List (String × String) := js.fold (λ as s j => (s, j.getStr!) :: as) []
  IO.mkRef $ HashMap.ofList l

/-- Replaces the TeX sequences in a string with their 
  corresponding Unicode characters using the `texcmds` list. -/
def teXToUnicode (s : String) : IO String := do
  match s.splitOn "\\" with
  | [] => return s
  | h :: ls =>  
    let us ← ls.mapM $ fun l => do
      match l.splitOn " " with
      | [] => pure ""
      | cmd :: ws =>
        let s ← findUnicodeReplacement cmd
        pure $ ws.foldl (· ++ " " ++ ·) s

    return .join (h :: us)

  where
    findUnicodeReplacement (cmd : String) : IO String := do
      if let .some u :=
          (← texCommandCache.get).find? cmd then
        pure u else
        pure <| "\\" ++ cmd


namespace List

def alternate : List α → List α × List α
  | [] => ([], [])
  | a :: as =>
    match alternate as with
      | (odds, evens) => (a :: evens, odds)

def interleave : List α → List α → List α
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs =>
    a :: b :: interleave as bs

theorem alternate_interleave : (l : List α) → 
  let (odds, evens) := l.alternate
  .interleave odds evens = l
  | [] => rfl
  | [a] => rfl
  | a :: a' :: as => by
    dsimp only [alternate, interleave]
    congr
    apply alternate_interleave

#eval [1, 2, 3, 4, 5, 6].alternate

end List


def openAIKey : IO (Option String) := IO.getEnv "OPENAI_API_KEY"

/-- Query open-ai with given prompt and parameters -/
-- this is delibrately different from the one in `Translate.lean`
-- this is to keep everything at the `IO` level without disturbing the rest of the code
def openAIQuery (prompt : String)
  (n : Nat := 1)
  (temp : JsonNumber := ⟨2, 1⟩)
  (stopTokens : Array String :=  #[":=", "-/"]) : IO Json := do

  let .some key ← openAIKey | panic! "OPENAI_API_KEY not set"
  
  let data := Json.mkObj [
    ("model", "code-davinci-002"), 
    ("prompt", prompt), 
    ("temperature", Json.num temp), 
    ("n", n), 
    ("max_tokens", 150), 
    ("stop", Json.arr <| stopTokens |>.map Json.str)
    ] |>.pretty
  
  let out ←  IO.Process.output {
        cmd:= "curl", 
        args:= #["https://api.openai.com/v1/completions",
        "-X", "POST",
        "-H", "Authorization: Bearer " ++ key,
        "-H", "Content-Type: application/json",
        "--data", data]}
  
  IO.ofExcept $ Json.parse out.stdout

def makePrompt (s : String) : IO String := do
  let promptPrefix := "
TeX: $a \\leq b \\leq c$
Lean: `a ≤ b ∧ b ≤ c`

TeX: $0, 1, 2, ..., 10$
Lean: `List.range 11`

TeX: $\\[0, 1\\]$
Lean: `Set.Icc 0 1`

TeX: $\\sum_{i=0}^1000 i^2$
Lean: `Finset.sum (Finset.range 1001) (fun x => x^2)`"

  return s!"{promptPrefix}\n\nTeX: ${s}$\nLean: `"

#eval do IO.println $ ← makePrompt "\\frac{1}{2}"

/-- Translates a string representing a TeX formula to the corresponding Lean code. -/
def teXToLean (s : String) : IO String := do
  let t ← teXToUnicode s
  -- needs a better heuristic for triggering Codex-based translation
  if t.contains '\\' then
    IO.println s!"Translating with Codex: {t}"
    let prompt ← makePrompt s
    let codexOutput ← openAIQuery prompt (stopTokens := #["$", "$$", "\\[", "\n"])
    let translation := codexOutput["choices"]![0]!["text"]!.getStr!
    return s!"`{translation}"
  else
    IO.println s!"Translated via Unicode mapping: {t}"
    return s!"`{t}`" 

/-- Extracts the TeX formulas within `$` or `$$` in the given string,
  translates them individually to Lean code, and then
  replaces them back with `\`` (backticks). -/
def translateTeX : String → IO String :=
  translateTeXAux "$$"
    (translateTeXAux "$" 
      pure 
      teXToLean)
    teXToLean
  where
    /-- Splits a string according to the delimiter.
        The substrings in the odd positions are processed as text,
        while those in the even positions are processed as formulas. -/
    translateTeXAux (teXDelimiter : String) 
      (modText : String → IO String) 
      (modFormula : String → IO String) :
          String → IO String := fun s => do
        let (text, formulas) := s.splitOn teXDelimiter |>.alternate
        let text' ← text.mapM modText
        let formulas' ← formulas.mapM modFormula
        let s' := .interleave text' formulas'
        return .join s'