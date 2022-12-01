import Lean

namespace SentenceSimilarity

/-- A structure with the necessary data for retrieving relevant `mathlib` statements by sentence similarity. -/
structure Params where
  /-- The `.json` file from which to take `mathlib` declarations. -/
  promptSource : String := "data/prompts.json"
  /-- The model to use for sentence embeddings. -/
  model : String := "all-mpnet-base-v2"
  /-- The kind of prompts to retrieve (`theorem`/`def`/etc.) -/
  kind : String
  /-- The field to extract from the `mathlib` data. -/
  field : String := "doc_string"
  /-- The number of relevant sentences to retrieve. -/
  numSim : Nat

/-- A `Request` comprises a statement and a collection of parameters. -/
structure Request extends Params where
  /-- The statement for which similar prompts are to be retrieved. -/
  stmt : String

/-- The IP address of the `LeanAide` server hosting the Python code. -/
def leanAideIP : IO String := do
  let some ip ← IO.getEnv "LEANAIDE_IP" | do 
    IO.println "Defaulting to local IP ..."
    pure "localhost:5000"
  return ip

def SentenceSimilarityQuery.toJson (req : SentenceSimilarity.Request) : IO <| Array Lean.Json := sorry