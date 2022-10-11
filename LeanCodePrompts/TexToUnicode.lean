import Lean
import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson
import LeanCodePrompts.ParseJson
import LeanCodePrompts.Utils

open Std Lean

initialize texCommandCache : IO.Ref (HashMap String String) ← do
  let js ← Json.parseFile "data/texcmds.json"
  let l := js.map $ fun j => (j[0]!.getStr!, j[1]!.getStr!)
  IO.mkRef $ HashMap.ofList l.toList

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

/-- Translates a string representing a TeX formula to the corresponding Lean code. -/
def teXToLean (s : String) : IO String := do
  -- a placeholder for actual code
  return "`formula`" 

/-- Extracts the TeX formulas within `$` or `$$` in the given string,
  translates them individually to Lean code, and then
  replaces them back with `\`` (backticks).
 -/
def translateTeX : String → IO String :=
  translateTeXAux "$$"
    (translateTeXAux "$" 
      pure 
      teXToLean)
    teXToLean
  where
    /-- Splits a string according to the delimiter.
        The substrings in the odd positions are processed as text,
        while those in the even positions are processed as formulas.
    -/
    translateTeXAux (teXDelimiter : String) 
      (modText : String → IO String) 
      (modFormula : String → IO String) :
          String → IO String := fun s => do
        let (text, formulas) := s.splitOn teXDelimiter |>.alternate
        let text' ← text.mapM modText
        let formulas' ← formulas.mapM modFormula
        let s' := .interleave text' formulas'
        return .join s'