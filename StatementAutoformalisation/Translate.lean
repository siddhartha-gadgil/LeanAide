import Lean
import StatementAutoformalisation.SentenceSimilarityQuery
import StatementAutoformalisation.KeywordExtractionQuery
import StatementAutoformalisation.LLMQuery

namespace Prompt

/-- A structure containing all the relevant information to build a prompt for a Codex query. -/
structure Params extends LLM.Params, SentenceSimilarity.Params, KeywordExtraction.Params where
  /-- Toggles whether to use a given set of fixed prompts (such as `Lean Chat` prompts) in the main prompt. -/
  fixedPrompts : Lean.MetaM <| Array DeclarationWithDocstring := pure #[]
  /-- A list of names of declarations from the environment that are to be used in the prompt. -/
  useNames : Array Lean.Name := #[]
  /-- A list of module names from which to gather declarations for the prompt. -/
  useModules : Array Lean.Name := #[]
  /-- Toggles whether to use declarations from the main context in the prompt. -/
  useMainCtx? : Bool := false
  /-- A method for printing a `Declaration` as a `String`. -/
  printDecl : ToString DeclarationWithDocstring := DeclarationWithDocstring.toString
  /-- Make the suffix to add at the end of the prompt. -/
  mkSuffix : String → String
  /-- An additional processing of the Codex completion before converting to a `DeclarationWithDocstring`. -/
  processCompletion : String → String := id

abbrev Params.toLLMParams : Prompt.Params → LLM.Params := Params.toParams
abbrev Params.toSentenceSimilarityParams : Prompt.Params → SentenceSimilarity.Params := Params.toParams_1
abbrev Params.toKeywordExtractionParams : Prompt.Params → KeywordExtraction.Params := Params.toParams_2

/-- A `Request` is a statement together with the relavent parameters for building a prompt. -/
structure Request extends Params where
  /-- The statement around which to build a prompt -/
  stmt : String

abbrev Request.params : Request → Params := Request.toParams_3

/-- All the declarations that go into creating the final prompt. -/
def promptDecls (req : Prompt.Request) : Lean.MetaM <| Array DeclarationWithDocstring := do
  let fixedPrompts ← req.fixedPrompts
  let similarityPrompts ← liftM <| SentenceSimilarity.Request.similarDecls ⟨req.toSentenceSimilarityParams, req.stmt⟩
  let keywordPrompts ← liftM <| KeywordExtraction.Request.similarDecls ⟨req.toKeywordExtractionParams, req.stmt⟩
  let customPrompts ← req.useNames.filterMapM DeclarationWithDocstring.fromName?
  let ctxPrompts ← DeclarationWithDocstring.envDecls req.useModules req.useMainCtx?
  let allPrompts := #[fixedPrompts, keywordPrompts, similarityPrompts, customPrompts, ctxPrompts]
  return allPrompts.foldl .append .empty

/-- Query the language model for translations based on the given `Prompt.Request`. -/
def translate (req : Prompt.Request) : Lean.MetaM <| Array DeclarationWithDocstring := do
  let decls ← promptDecls req
  let prompt := @buildPrompt req.printDecl decls <| req.mkSuffix req.stmt
  let completions ← LLM.Request.getLLMCompletions ⟨req.toLLMParams, prompt⟩
  completions |>.map req.processCompletion |>.filterMapM' DeclarationWithDocstring.fromString?

/-- Retrieve translations for a given `Prompt.Request` and sort them according to whether they type-check. -/
def typecheckTranslations (req : Prompt.Request) : Lean.Elab.Term.TermElabM <| Array DeclarationWithDocstring × Array (DeclarationWithDocstring × String) := do
  let decls ← translate req 
  let (typecorrect, failed) ← decls.partitionExceptM DeclarationWithDocstring.typeCheck
  return (typecorrect.map Prod.fst, failed)

end Prompt