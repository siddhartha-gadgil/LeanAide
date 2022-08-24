import Lean

namespace Lean.Json

def parseArrIO (s : String) : IO <| Array Json := do
  IO.ofExcept $ Json.parse s >>= Json.getArr?

def parseFile (path : System.FilePath) : IO <| Array Json :=
  IO.FS.readFile path >>= Json.parseArrIO

instance : GetElem Json String Json (λ j k => Except.toBool <| j.getObjVal? k) where
  getElem := λ j key h =>
    match j.getObjVal? key, h with
      | .ok j, _ => j
      | .error _, h => by simp [Except.toBool] at h

end Lean.Json


open Lean IO


section MathlibStatements

def MathlibStatements : IO <| Array Json := 
  Json.parseFile "LeanCodePrompts/KeywordSummary/full_mathlib_keyword_summary.json"

def fetchRelevantStatements (kw : String) : IO <| Array Json := do
  return (← MathlibStatements).filter $ (Option.toBool <| ·["keywords"]? >>= (·[kw]?))

def fetchModifiedStatements (mod : Json → α) (kw : String) : IO <| Array α := do
  return (← fetchRelevantStatements kw).map mod

def fetchModifiedStatementsM (mod : Json → IO α) (kw : String) : IO <| Array α := do
  (← fetchRelevantStatements kw).mapM mod

abbrev fetchRelevantDocstrings := 
  fetchModifiedStatementsM (ofExcept <| Json.getStr? ·["doc_string"]!)

def sentenceSimPairs (s : String) : IO <| Array (String × String) := do
  (← Json.parseArrIO s).mapM (
    let dict := ·["dct"]!
    return (← IO.ofExcept <| dict["doc_string"]!.getStr?, ← IO.ofExcept <| dict["theorem"]!.getStr?) )

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
def extractKeywordsToJson (s : String) : IO Json := do
  let processOutput (lines : List String) : Json :=
    let lines := lines |>.tail! |>.tail! |>.dropLast
    let processedLines := lines.map $ λ l => 
      match l.splitOn "0." with
        | [stmt, score] => (stmt.trim, Json.num ("0." ++ score).toJsonNumber!)
        | _ => panic! "Invalid format."
    Json.mkObj processedLines

  return processOutput <| ← yakeResults s

def extractKeywords (s : String) : IO <| List String := do
  let kws := (← yakeResults s) |>.tail! |>.tail! |>.dropLast
  return kws.map $ λ l =>
    String.splitOn l "0." |>.head! |>.trim

def extractKeywordsWithScores (s : String) : IO <| List (String × Float) := do
  let kws := (← yakeResults s) |>.tail! |>.tail! |>.dropLast
  return kws.map $ λ l =>
    match l.splitOn "0." with
      | [stmt, score] => (stmt.trim, ("0." ++ score).toFloat!)
      | _ => panic! "Invalid format."

/-- This function is meant for rapid visualisation of the `yake` output.
The keywords here *are* arranged in the order of relevance. -/
def yakeOutput (s : String) : IO Unit := do
  for l in (← yakeResults s) do
    IO.println l

def fetchAllRelevantStatements (s : String) : IO <| Array Json := do
  let kws ← extractKeywords s
  let stmts ← kws.mapM fetchRelevantStatements
  return stmts.foldl .append .empty

def fetchAllModifiedStatementsM (mod : Json → IO α) (s : String) : IO <| Array α := do
  let kws ← extractKeywords s
  let stmts ← kws.mapM <| fetchModifiedStatementsM mod
  return stmts.foldl .append .empty

abbrev fetchAllRelevantDocstrings :=
  fetchAllModifiedStatementsM (ofExcept <| Json.getStr? ·["doc_string"]!)

end Yake


section Experiments

def keyword := "abelian group"

-- #eval do
--  for docstr in (← fetchRelevantDocstrings keyword) do
--    IO.println docstr



def statement := "Every finite integral domain is a field."

#eval yakeOutput statement

end Experiments
