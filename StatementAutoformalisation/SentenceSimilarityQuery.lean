import Lean
import StatementAutoformalisation.Declaration
import StatementAutoformalisation.LeanAideIP

namespace SentenceSimilarity

/-- A structure with the necessary data for retrieving relevant `mathlib` statements by sentence similarity. -/
structure Params where
  /-- The `.json` file from which to take `mathlib` declarations. -/
  source : String := "data/prompts.json"
  /-- The `SentenceTransformers` model to use for sentence embeddings. -/
  sentenceTransformersModel : String := "all-mpnet-base-v2"
  /-- The kind of prompts to retrieve (`theorem`/`def`/etc.) -/
  kind : String
  /-- The field to extract from the `mathlib` data. -/
  field : String := "doc_string"
  /-- The number of relevant sentences to retrieve. -/
  nSim : Nat
deriving Repr

/-- A `Request` comprises a statement and a collection of parameters. -/
structure Request extends Params where
  /-- The statement for which similar prompts are to be retrieved. -/
  stmt : String
deriving Repr

/-- Render a `Request` in `JSON` format. -/
def Request.toJson (req : SentenceSimilarity.Request) : Lean.Json := .mkObj [
  ("filename", req.source),
  ("model_name", req.sentenceTransformersModel),
  ("kind", req.kind),
  ("field", req.field),
  ("n", req.nSim),
  (req.field, req.stmt)
]

/-- Retrieve relevant declarations from `mathlib` via similarity of sentence embeddings. -/
def Request.similarDecls (req : SentenceSimilarity.Request) : IO <| Array DeclarationWithDocstring := 
  match req.nSim with
    | .zero => return #[]
    | _ => do
    let out ← IO.Process.output {cmd:= "curl", args:= #[
      "-X", "POST", 
      "-H", "Content-Type: application/json", 
      "--data", req.toJson.pretty, s!"{← leanAideIP}/nearest_prompts"]}
    IO.ofExcept <| do
      let result ← Lean.Json.parse out.stdout
      let prompts ← result.getArr?
      prompts.mapM DeclarationWithDocstring.fromJson

/-- Accept multiple sentence similarity requests and merge them into a single array. -/
def mergeRequests (reqs : Array SentenceSimilarity.Request) : IO <| Array DeclarationWithDocstring := do
  let decls ← reqs.mapM Request.similarDecls
  -- for now, the merging is done by just appending the data received from each request
  -- TODO eventually use similarity scores to rank the declarations 
  return decls.foldl .append .empty

end SentenceSimilarity

section Test

def SentenceSimilarity.egReq : SentenceSimilarity.Request :=
{ kind := "theorem", nSim := 5, stmt := "Every matrix satisfies its own characteristic polynomial." }

-- #eval SentenceSimilarity.egReq.similarDecls

end Test