import Lean
import StatementAutoformalisation.Declaration

namespace KeywordExtraction

/-- A structure with the necessary data for retrieving relevant `mathlib` statements by keyword extraction. -/
structure Params where
  /-- The number of relevant sentence to retrieve. -/
  nKw : Nat
deriving Repr

/-- A `Request` comprises a statement and a collection of parameters. -/
structure Request extends Params where
  /-- The statement for which similar prompts are to be retrieved. -/
  stmt : String
deriving Repr

/-- Extract the mathematical keywords from a given sentence. -/
def extractKeywords : String → IO (Array String) := sorry

/-- Retrieve declarations from `mathlib` that share keywords with the given sentence. -/
def Request.similarDecls (req : KeywordExtraction.Request) : IO <| Array DeclarationWithDocstring :=
  match req.nKw with
    | .zero => return #[]
    | _ => return #[]
    -- TODO implement this function 
    -- sorry

end KeywordExtraction