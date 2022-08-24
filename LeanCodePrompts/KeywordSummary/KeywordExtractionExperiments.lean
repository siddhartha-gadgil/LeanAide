import LeanCodePrompts.KeywordSummary.KeywordExtraction
import LeanCodePrompts.ParseJson

open Lean

def MathlibKeywordLookup : MetaM Json := do
  readJson $ ← IO.FS.readFile 
    "LeanCodePrompts/KeywordSummary/mathlib_keyword_lookup.json"

#check liftOption

def fetchStatementsWithKeyword (mod : Json → α) (kw : String) : MetaM <| Array α := do
  let mathlibStmts ← MathlibStatements
  let mathlibKwds ← MathlibKeywordLookup
  let arr : Option <| Array α := do
    let idxsJ ← mathlibKwds[kw]?
    let idxs ← idxsJ.getArr?.toOption
    idxs.mapM $ λ idxJ => do
      let idx ← idxJ.getNat?.toOption
      let stmt ← mathlibStmts.get? idx
      return mod stmt

  match arr with
    | some arr => return arr
    | none => return #[]

#eval fetchStatementsWithKeyword id "vector bundle" -- the `id` is to perform no modification to the output

#eval fetchStatementsWithKeyword (·["statement"]!) "forgetful functor" -- extracting only the statements

#eval fetchStatementsWithKeyword (·["keywords"]!["free group"]!) "free group" -- extracting the scores associated with the keyword "free group"


#eval fetchStatementsWithKeyword (·["doc_string"]!) "free group"

#eval fetchStatementsWithKeyword (·["doc_string"]!) "free"

def docPair (js: Json) : String × String := 
  ((js["doc_string"]!).getStr?.toOption.get!, (js["theorem"]!).getStr?.toOption.get!)

def pair :=  fetchStatementsWithKeyword docPair "free group"

#eval pair

def keywordBasedPrompts (mod : Json → α) (s : String) : MetaM <| Array α := do
  let kwdsScores ← extractKeywordsWithScores s
  let prompts ← kwdsScores.mapM (λ ⟨kw, score⟩ => do
    -- getting the top 3 entries
    -- the number of entries fetched can be a function of the relevance
    return (← fetchStatementsWithKeyword mod kw).extract 0 4)
  return prompts.foldl Array.append #[]

#eval keywordBasedPrompts (·["doc_string"]!) "Every subgroup of a free group is a free group" 

#eval extractKeywordsWithScores "Every subgroup of a free group is a free group"
