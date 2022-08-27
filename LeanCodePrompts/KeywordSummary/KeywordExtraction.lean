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

def getStr! (j : Json) : String :=
  j.getStr?.toOption.get!

end Lean.Json


open Lean IO


section MathlibStatements

def MathlibStatements : IO <| Array Json := 
  Json.parseFile "LeanCodePrompts/KeywordSummary/full_mathlib_keyword_summary.json"

initialize mathlibCache : IO.Ref (Array Json) ← IO.mkRef (← MathlibStatements)

def getMathlibStatements : IO (Array Json) := do mathlibCache.get


def fetchRelevantStatements (kw : String) : IO <| Array Json := do
  return (← getMathlibStatements).filter $ (Option.toBool <| ·["keywords"]? >>= (·[kw]?))

def fetchModifiedStatements (mod : Json → α) (kw : String) : IO <| Array α := do
  return (← fetchRelevantStatements kw).map mod

def fetchModifiedStatementsM (mod : Json → IO α) (kw : String) : IO <| Array α := do
  (← fetchRelevantStatements kw).mapM mod

abbrev fetchRelevantDocstrings := 
  fetchModifiedStatements (·["doc_string"]!.getStr!)

-- def sentenceSimPairs (s : String) : IO <| Array (String × String) := do
--   (← Json.parseArrIO s).mapM (
--     let dict := ·["dct"]!
--     return (dict["doc_string"]!.getStr!, dict["theorem"]!.getStr!) )

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

def extractKeywordsWithScores (s : String) (out : Bool := false) : IO <| List (String × Float) := do
  let kwds ← yakeResults s

  if out then
    for l in kwds do
      IO.println l

  let kwds := kwds |>.tail! |>.tail! |>.dropLast
  return kwds.map $ λ l =>
    match l.splitOn "0." with
      | [stmt, score] => (stmt.trim, ("0." ++ score).toFloat!)
      | _ => panic! "Invalid format."

def extractKeywords (s : String) (out : Bool := false) : IO <| List String := do
  let kwdsWithScores ← extractKeywordsWithScores s out
  return kwdsWithScores.map Prod.fst

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
  fetchAllModifiedStatementsM (IO.ofExcept <| Json.getStr? ·["doc_string"]!)

end Yake


section KeywordLookup

def MathlibKeywordLookup : IO Json := do
  let file ← IO.FS.readFile 
    "LeanCodePrompts/KeywordSummary/mathlib_keyword_lookup.json"
  IO.ofExcept <| Json.parse file

initialize keywordCache : IO.Ref (Std.HashMap String (Array Nat)) ← do
  let mathlibKwdsJson ← IO.ofExcept (← MathlibKeywordLookup).getObj?
  
  let mathlibKwds : List (String × Array Nat) :=
    mathlibKwdsJson.fold ( λ l kw idxsJ =>

      let idxs : Array Nat := Option.get! do
        let idxs? ← idxsJ.getArr?.toOption
        idxs?.mapM (·.getNat?.toOption)

      (kw, idxs) :: l ) []

  IO.mkRef (Std.HashMap.ofList mathlibKwds)

def getKeywordIndices? (kw : String) : IO <| Option (Array Nat) := do
  let cache ← keywordCache.get
  return cache.find? kw


def fetchStatementsWithKeyword (mod : Json → α) (kw : String) : IO <| Array α := do
  let mathlibStmts ← getMathlibStatements
  match ← getKeywordIndices? kw with
    | some idxs => return idxs.map <| (mathlibStmts.get! · |> mod)
    | none => return #[]

def fetchStatementsWithKeywordM (mod : Json → IO α) (kw : String) : IO <| Array α := do
  let mathlibStmts ← getMathlibStatements
  match ← getKeywordIndices? kw with
    | some idxs => idxs.mapM <| (mathlibStmts.get! · |> mod)
    | none => return #[]

def docPair (js: Json) : String × String := 
  (js["doc_string"]!.getStr!, js["theorem"]!.getStr!)

def keywordBasedPrompts (mod : Json → α) (s : String) (number : Nat := 4)(scoreBound: Float := 0.2)(matchBound: Nat := 15) (kwds : Bool := false) : IO <| Array α := do
  let kwdsScores ← extractKeywordsWithScores s (out := kwds)
  let prompts ← kwdsScores.mapM (λ ⟨kw, score⟩ => do
    if score > scoreBound then return #[]
    else 
    let statements ← fetchStatementsWithKeyword mod kw
    if statements.size > matchBound then return #[]
    else
    return statements.extract 0 number)
  return prompts.foldl Array.append #[]

end KeywordLookup

