import StatementAutoformalisation.Interface
import StatementAutoformalisation.Config.FixedPrompts

namespace Default

def LLMParams : LLM.Params :=
{
  openAIModel := "code-davinci-002",
  temperature := 8,
  n := 7,
  maxTokens := 300,
  stopTokens := #[":=", "\n\n/-", "\n/-", "/-"]
}

def SentenceSimilarityParams : SentenceSimilarity.Params :=
{
  source := "data/safe-prompts.json",
  sentenceTransformersModel := "all-mpnet-base-v2",
  kind := "theorem",
  field := "doc_string",
  nSim := 15
}

def KeywordExtractionParams : KeywordExtraction.Params :=
{
  nKw := 0
}


/-- The expected `kind` (`theorem`/`def`/...) of the completion.
  This variable is required only to modify the suffix of the main prompt. -/
def expectedKind? : Option String := "theorem"

def PromptParams : Prompt.Params :=
{
  toLLMParams := LLMParams, 
  toSentenceSimilarityParams := #[SentenceSimilarityParams], 
  toKeywordExtractionParams := #[KeywordExtractionParams],
  fixedPrompts := leanChatPrompts,
  useNames := #[],
  useModules := #[],
  useMainCtx? := false,
  printDecl := DeclarationWithDocstring.toString
  mkSuffix := fun stmt => s!"{printAsComment stmt}\n{expectedKind?.getD ""}",
  processCompletion := fun comment completion => s!"{printAsComment comment}\n{expectedKind?.getD ""} {completion}"
}

def InterfaceParams : Interface.Params DeclarationWithDocstring :=
{
  title := "Translate comment to Lean theorem statement (with default settings).",
  nearestOccurrence? := nearestComment,
  extractText? := extractCommentText?,
  action := fun stmt =>
    Prompt.typecorrectTranslations ⟨PromptParams, stmt⟩ >>= (pure ·[0]!),
  postProcess := fun _ => ToString.toString
}

@[codeActionProvider] def Action := performCodeAction InterfaceParams

end Default