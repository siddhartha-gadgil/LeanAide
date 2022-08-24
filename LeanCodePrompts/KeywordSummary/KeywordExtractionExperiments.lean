import LeanCodePrompts.KeywordSummary.KeywordExtraction
import LeanCodePrompts.ParseJson

open Lean

def MathlibKeywordLookup : MetaM Json := do
  readJson $ ← IO.FS.readFile 
    "LeanCodePrompts/KeywordSummary/mathlib_keyword_lookup.json"


def fetchStatementsWithKeyword (mod : Json → α) (kw : String) : MetaM <| Array α := do
  let mathlibStmts ← MathlibStatements
  match (← MathlibKeywordLookup)[kw]!.getArr? with
    | .ok idxs => return idxs.filterMap $ λ idx => 
        idx.getNat?.toOption >>= mathlibStmts.get? >>= (some <| mod ·)
    | .error _ => return #[]

#eval fetchStatementsWithKeyword id "vector bundle" -- the `id` is to perform no modification to the output

#eval fetchStatementsWithKeyword (·["statement"]!) "forgetful functor" -- extracting only the statements

#eval fetchStatementsWithKeyword (·["keywords"]!["free group"]!) "free group" -- extracting the scores associated with the keyword "free group"


def keywordBasedPrompts (mod : Json → α) (s : String) : MetaM <| Array α := do
  let kwdsScores ← extractKeywordsWithScores s
  let prompts ← kwdsScores.mapM (λ ⟨kw, score⟩ => do
    -- getting the top 3 entries
    -- the number of entries fetched can be a function of the relevance
    return (← fetchStatementsWithKeyword mod kw).extract 0 2)
  return prompts.foldl Array.append #[]

#eval keywordBasedPrompts (·["doc_string"]!) "Every free group is free"
