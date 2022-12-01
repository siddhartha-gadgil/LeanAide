import LeanCodePrompts.Declaration

/-- A structure with all the relevant information for making a query to OpenAI Codex. -/
structure CodexQuery where
  /-- The main prompt supplied to Codex. -/
  prompt : String
  /-- The Codex model to use. -/
  model : String := "code-davinci-002"
  /-- The temperature at which to generate the completion. 
      This is stored as a natural number representing the actual temperature scaled up by a factor of ten. -/
  temperature : Nat := 6
  /-- The number of completions to generate. -/
  n : Nat
  /-- The maximum allowed number of tokens in the completion. -/
  maxTokens : Nat := 300
  /-- The stop tokens for the completion. -/
  stopTokens : List String := [":=", "\n\n/-", "\n/-", "/-"]

/-- A structure with the necessary data for retrieving relevant `mathlib` statements by sentence similarity. -/
structure SentenceSimilarityQuery where
  /-- The `.json` file from which to take `mathlib` declarations. -/
  promptSource : String := "data/prompts.json"
  /-- The model to use for sentence embeddings. -/
  model : String := "all-mpnet-base-v2"
  /-- The field to extract from the `mathlib` data. -/
  field : String := "doc_string"
  /-- The statement for which similar prompts are to be retrieved. -/
  stmt : String
  /-- The number of relevant sentences to retrieve. -/
  numSim : Nat

/-- A structure with the necessary data for retrieving relevant `mathlib` statements by keyword extraction. -/
structure KeywordQuery where
  /-- The statement for which similar prompts are to be retrieved. -/
  stmt : String
  /-- The number of relevant sentence to retrieve. -/
  numKw : Nat

/-- A structure containing all the relevant information to build a prompt for a Codex query. -/
structure PromptQuery extends SentenceSimilarityQuery, KeywordQuery where
  /-- Toggles whether to use a given set of fixed prompts (such as `Lean Chat` prompts) in the main prompt. -/
  useFixed? : Bool := true
  /-- Toggles whether to use declarations from the context in the prompt. -/
  useCtx? : Bool := false
  /-- A list of names of declarations from the environment that are to be used in the prompt. -/
  useNames : List Lean.Name := []
  /-- A method for printing a `Declaration` as a `String`. -/
  [printDecl : ToString Declaration]