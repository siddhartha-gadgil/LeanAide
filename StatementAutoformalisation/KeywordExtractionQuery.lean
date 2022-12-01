import Lean

namespace KeywordExtraction

/-- A structure with the necessary data for retrieving relevant `mathlib` statements by keyword extraction. -/
structure Params where
  /-- The number of relevant sentence to retrieve. -/
  numKw : Nat

/-- A `Request` comprises a statement and a collection of parameters. -/
structure Request extends Params where
  /-- The statement for which similar prompts are to be retrieved. -/
  stmt : String

end KeywordExtraction