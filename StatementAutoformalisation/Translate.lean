import Lean
import StatementAutoformalisation.SentenceSimilarityQuery
import StatementAutoformalisation.KeywordExtractionQuery
import StatementAutoformalisation.LLMQuery

namespace Prompt

/-- A structure containing all the relevant information to build a prompt for a Codex query. -/
structure Params extends LLM.Params, SentenceSimilarity.Params, KeywordExtraction.Params where
  /-- Toggles whether to use a given set of fixed prompts (such as `Lean Chat` prompts) in the main prompt. -/
  fixedPrompts : Array DeclarationWithDocstring := #[]
  /-- A list of names of declarations from the environment that are to be used in the prompt. -/
  useNames : Array Lean.Name := #[]
  /-- Toggles whether to use declarations from the context in the prompt. -/
  useCtx? : Bool := false
  /-- A method for printing a `Declaration` as a `String`. -/
  printDecl : ToString DeclarationWithDocstring := DeclarationWithDocstring.toString

abbrev Params.toLLMParams : Prompt.Params → LLM.Params := Params.toParams
abbrev Params.toSentenceSimilarityParams : Prompt.Params → SentenceSimilarity.Params := Params.toParams_2
abbrev Params.toKeywordExtractionParams : Prompt.Params → KeywordExtraction.Params := Params.toParams_1

/-- A `Request` is a statement together with the relavent parameters for building a prompt. -/
structure Request extends Params where
  /-- The statement around which to build a prompt -/
  stmt : String
  /-- Make the suffix to add at the end of the prompt. -/
  mkSuffix : Params → String → String
  /-- Process the language model completion as a `DeclarationWithDocstring`. -/
  processCompletion : Params → String → DeclarationWithDocstring
  /-- Whether to retain only the type-correct completions. -/
  typecheck? : Bool := true

abbrev Request.params : Request → Params := Request.toParams_2

/-- All the declarations that go into creating the final prompt. -/
def promptDecls (req : Prompt.Request) : Lean.MetaM <| Array DeclarationWithDocstring := do
  let fixedPrompts := req.fixedPrompts
  let similarityPrompts ← liftM <| SentenceSimilarity.Request.similarDecls ⟨req.toSentenceSimilarityParams, req.stmt⟩
  let keywordPrompts ← liftM <| KeywordExtraction.Request.similarDecls ⟨req.toKeywordExtractionParams, req.stmt⟩
  let customPrompts ← req.useNames.filterMapM DeclarationWithDocstring.fromName?
  let ctxPrompts ← if req.useCtx? then DeclarationWithDocstring.envDecls else pure #[]
  let allPrompts := #[fixedPrompts, keywordPrompts, similarityPrompts, customPrompts, ctxPrompts]
  return allPrompts.foldl .append #[]
  
/-- Query the language model for translations based on the given `Prompt.Request`. -/
def translate (req : Prompt.Request) : Lean.MetaM <| Array DeclarationWithDocstring := do
  let decls ← promptDecls req
  let prompt := buildPrompt decls <| req.mkSuffix req.params req.stmt
  let completions ← LLM.Request.getLLMCompletions ⟨req.toLLMParams, prompt⟩
  let out := completions.map <| req.processCompletion req.params
  if req.typecheck? then 
    out.filterM DeclarationWithDocstring.typeCheck
  else 
    return out

end Prompt