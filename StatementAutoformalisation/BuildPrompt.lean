import Lean
import StatementAutoformalisation.SentenceSimilarityQuery
import StatementAutoformalisation.KeywordExtractionQuery
import StatementAutoformalisation.Declaration

/-- A structure containing all the relevant information to build a prompt for a Codex query. -/
structure Prompt.Params extends SentenceSimilarity.Params, KeywordExtraction.Params where
  /-- Toggles whether to use a given set of fixed prompts (such as `Lean Chat` prompts) in the main prompt. -/
  useFixed? : Bool := true
  /-- Toggles whether to use declarations from the context in the prompt. -/
  useCtx? : Bool := false
  /-- A list of names of declarations from the environment that are to be used in the prompt. -/
  useNames : List Lean.Name := []
  /-- A method for printing a `Declaration` as a `String`. -/
  [printDecl : ToString Declaration]