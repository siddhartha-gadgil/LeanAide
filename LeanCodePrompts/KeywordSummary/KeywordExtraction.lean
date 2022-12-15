import Lean
import LeanCodePrompts.Utils

open Lean IO

section MathlibStatements

def MathlibStatements : IO <| Array Json := 
  Json.parseFile "data/full_mathlib_keyword_summary.json"

initialize mathlibCache : IO.Ref (Array Json) ← IO.mkRef .empty

def getMathlibStatements : IO (Array Json) := do 
  let mathlibStmts ← mathlibCache.get
  if mathlibStmts.isEmpty then
    let stmts ← MathlibStatements
    mathlibCache.set stmts
    return stmts
  else return mathlibStmts

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

def leanAideIP : IO String := do
  let key? ← IO.getEnv "LEANAIDE_IP"
  return key?.getD "localhost:5000"

/-- Fetch the keyword extraction results from `YAKE` (Yet Another Keyword Extractor). -/
def yakeResults (s : String) : IO (Array Json) := do
  let out ← IO.Process.output {cmd:= "curl", args:= 
          #["-X", "POST", 
            "-H", "Content-type: application/json", 
            "-d", s, s!"{← leanAideIP}/keywords"]}
  Json.parseArrIO out.stdout

def extractKeywordsWithScores (s : String) (out : Bool := false) : IO <| List (String × Float) := do
  let kwds ← yakeResults s
  let kwds := kwds.toList

  if out then
    for l in kwds do
      IO.println l

  return kwds.filterMap $ λ j =>
    let j' := Except.toOption j.getArr? |>.get!
    let kw := j'[0]!.getStr!
    let score? := j'[1]!.getNum?
    let score := (Except.toOption score?).get! |>.toFloat
    return (kw, score)

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
    "data/mathlib_keyword_lookup.json"
  IO.ofExcept <| Json.parse file

initialize keywordCache : IO.Ref (HashMap String (Array Nat)) ← IO.mkRef .empty

def getKeywordCache : IO <| HashMap String (Array Nat) := do
  let cache ← keywordCache.get
  if cache.isEmpty then
    let mathlibKwdsJson ← IO.ofExcept (← MathlibKeywordLookup).getObj?
  
    let mathlibKwds : List (String × Array Nat) :=
    mathlibKwdsJson.fold ( λ l kw idxsJ =>

      let idxs : Array Nat := Option.get! do
        let idxs? ← idxsJ.getArr?.toOption
        idxs?.mapM (·.getNat?.toOption)

      (kw, idxs) :: l ) []
    
    let keywordHash := HashMap.ofList mathlibKwds
    keywordCache.set keywordHash
    return keywordHash
  else return cache

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

