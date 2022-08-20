import Lean

#check Except.toBool

namespace Lean.Json

def parseFile (path : System.FilePath) : IO <| Array Json := do
  IO.ofExcept $ Json.parse (← IO.FS.readFile path) >>= Json.getArr?

instance : GetElem Json String Json (λ j k => Except.toBool <| j.getObjVal? k) where
  getElem := λ j key h =>
    match j.getObjVal? key, h with
      | .ok j, _ => j
      | .error _, h => by simp [Except.toBool] at h

end Lean.Json


open Lean IO

section MathlibStatements

def MathlibStatements : IO <| Array Json := 
  Json.parseFile "OpenaiModelPrompting/KeywordSummary/full_mathlib_keyword_summary.json"

def fetchRelevantStatements (kw : String) : IO <| Array Json := do
  (← MathlibStatements).filterM $ λ j => 
    return ( Except.toBool $ j.getObjVal? "keywords" >>= (Json.getObjVal? · kw) )

def fetchModifiedStatements (mod : Json → α) (kw : String) : IO <| Array α := do
  return (← fetchRelevantStatements kw).map mod

def fetchModifiedStatementsM (mod : Json → IO α) (kw : String) : IO <| Array α := do
  (← fetchRelevantStatements kw).mapM mod

abbrev fetchRelevantDocstrings := 
  fetchModifiedStatementsM (ofExcept $ Json.getObjVal? · "doc_string")

end MathlibStatements


namespace String

def toFloat! (s : String) : Float :=
  match (Syntax.decodeScientificLitVal? s) with
    | some (m, sign, e) => OfScientific.ofScientific m sign e
    | none => panic! s!"Failed to parse {s}"

/- This is already in `src/Lean/Data/Json/Basic.lean`,
  but fails to get picked up by Lean here. -/
instance : Inhabited JsonNumber := ⟨0⟩

def toJsonNumber! (s : String) : JsonNumber :=
  match (Syntax.decodeScientificLitVal? s) with
    | some (m, _, e) => JsonNumber.mk m e
    | none => panic! s!"Failed to parse {s}"

end String


section Yake

/-- Running the code in this section requires `Yet Another Keyword Extractor (Yake)` - https://pypi.org/project/yake/.
This package can be installed with `pip3 install -U yake`.-/

def yakeResults (s : String) : IO <| List String := do
  let out ← Process.output 
      {cmd := "yake", args := #["--text_input", s, "--verbose"]}
  return out.stdout |>.splitOn "\n"

/- The keywords are not necessarily ranked by relevance in the output Json. -/
def extractKeywords (s : String) : IO Json := do
  let processOutput (lines : List String) : Json :=
    let lines := lines |>.tail! |>.tail! |>.dropLast
    let processedLines := lines.map $ λ l => 
      match l.splitOn "0." with
        | [stmt, score] => (stmt.trim, Json.num ("0." ++ score).toJsonNumber!)
        | _ => panic! "Invalid format."
    Json.mkObj processedLines

  return processOutput <| ← yakeResults s

/-- This function is meant for rapid visualisation of the `yake` output.
The keywords here *are* arranged in the order of relevance. -/
def yakeOutput (s : String) : IO Unit := do
  for l in (← yakeResults s) do
    IO.println l

end Yake

def main : IO Unit := do
  println "Reading file..."
  let mathlibStmts ← Json.parseFile "data/clean_prompts.json"
  println "Annotating with keywords..."
  let mathlibStmtsWithKeywords ← mathlibStmts.mapM $ λ j => do
    let docstring ← ofExcept <| Json.getStr? j["doc_string"]!
    return j.setObjVal! "keywords" (← extractKeywords docstring)
  println "Writing to output..."
  FS.writeFile "OpenaiModelPrompting/KeywordSummary/full_mathlib_keyword_summary.json" $ (Json.arr mathlibStmtsWithKeywords).compress
  println "Done!"
  
  