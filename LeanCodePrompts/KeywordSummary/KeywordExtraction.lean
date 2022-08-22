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

#eval do
  for docstr in (← fetchRelevantDocstrings keyword) do
    IO.println docstr



def statement := "Every finite integral domain is a field."

#eval yakeOutput statement

end Experiments


def egJsonSentenceSim : String := "[{\"score\": 0.7298493385314941, \"dct\": {\"name\": \"nat.prime.mod_two_eq_one_iff_ne_two\", \"statement\": \"theorem nat.prime.mod_two_eq_one_iff_ne_two {p : ℕ} [fact (nat.prime p)] : p % 2 = 1 ↔ p ≠ 2\", \"theorem\": \"{p : ℕ} [fact (nat.prime p)] : p % 2 = 1 ↔ p ≠ 2\", \"args\": \"{p : ℕ} [fact (nat.prime p)]\", \"doc_string\": \"A prime `p` satisfies `p % 2 = 1` if and only if `p ≠ 2`.\", \"type\": \"p % 2 = 1 ↔ p ≠ 2\"}}, {\"score\": 0.57069331407547, \"dct\": {\"name\": \"nat.odd_mod_four_iff\", \"statement\": \"theorem nat.odd_mod_four_iff {n : ℕ} : n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3\", \"theorem\": \"{n : ℕ} : n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3\", \"args\": \"{n : ℕ}\", \"doc_string\": \"A natural number is odd iff it has residue `1` or `3` mod `4`\", \"type\": \"n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3\"}}, {\"score\": 0.5074306726455688, \"dct\": {\"name\": \"nat.factorization_eq_zero_iff\", \"statement\": \"theorem nat.factorization_eq_zero_iff (n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1\", \"theorem\": \"(n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1\", \"args\": \"(n : ℕ)\", \"doc_string\": \"The only numbers with empty prime factorization are `0` and `1`\", \"type\": \"n.factorization = 0 ↔ n = 0 ∨ n = 1\"}}, {\"score\": 0.4935227930545807, \"dct\": {\"name\": \"nat.prime.factorization\", \"statement\": \"theorem nat.prime.factorization {p : ℕ} (hp : nat.prime p) : p.factorization = finsupp.single p 1\", \"theorem\": \"{p : ℕ} (hp : nat.prime p) : p.factorization = finsupp.single p 1\", \"args\": \"{p : ℕ} (hp : nat.prime p)\", \"doc_string\": \"The only prime factor of prime `p` is `p` itself, with multiplicity `1`\", \"type\": \"p.factorization = finsupp.single p 1\"}}]"

def sentenceSimPairs (s : String) : IO <| Array (String × String) := do
  (← Json.parseArrIO s).mapM (
    let dict := ·["dct"]!
    return (← IO.ofExcept <| dict["doc_string"]!.getStr?, ← IO.ofExcept <| dict["theorem"]!.getStr?) )

#eval sentenceSimPairs egJsonSentenceSim
