import Lean
import StatementAutoformalisation.Declaration
import StatementAutoformalisation.LeanAideIP

namespace SentenceSimilarity

/-- A structure with the necessary data for retrieving relevant `mathlib` statements by sentence similarity. -/
structure Params where
  /-- The `.json` file from which to take `mathlib` declarations. -/
  source : String := "data/prompts.json"
  /-- The model to use for sentence embeddings. -/
  model : String := "all-mpnet-base-v2"
  /-- The kind of prompts to retrieve (`theorem`/`def`/etc.) -/
  kind : String
  /-- The field to extract from the `mathlib` data. -/
  field : String := "doc_string"
  /-- The number of relevant sentences to retrieve. -/
  nSim : Nat

/-- A `Request` comprises a statement and a collection of parameters. -/
structure Request extends Params where
  /-- The statement for which similar prompts are to be retrieved. -/
  stmt : String

/-- Render a `Request` in `JSON` format. -/
def Request.toJson (req : SentenceSimilarity.Request) : Lean.Json := .pretty <| .mkObj [
  ("filename", req.source),
  ("model_name", req.model),
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
      "-H", "Content-type: application/json", 
      "-d", req.toJson.compress, s!"{← leanAideIP}/nearest_prompts"]}
    IO.ofExcept <| do 
      let result ← Lean.Json.parse out.stdout
      let prompts ← result.getArr?
      prompts.mapM DeclarationWithDocstring.fromJson

end SentenceSimilarity