import CodeAction.Interface
import StatementAutoformalisation.Translate
import StatementAutoformalisation.Config.FixedPrompts

namespace Custom

def LLMParams : LLM.Params :=
{
  openAIModel := "code-davinci-002",
  temperature := 2,
  n := 1,
  maxTokens := 200,
  stopTokens := #[":=", "\n\n/-", "\n/-", "/-"]
}

def SentenceSimilarityParams : SentenceSimilarity.Params :=
{
  source := "data/prompts.json",
  sentenceTransformersModel := "all-mpnet-base-v2",
  kind := "theorem",
  field := "doc_string",
  nSim := 10
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
  title := "Translate comment to Lean theorem statement (with custom settings).",
  nearestOccurrence? := nearestComment,
  extractText? := extractCommentText?,
  action := fun stmt =>
    Prompt.typecorrectTranslations ⟨PromptParams, stmt⟩ >>= (pure ·[0]!),
  postProcess := fun _ => DeclarationWithDocstring.toString.toString
}

@[codeActionProvider] def Action := performCodeAction InterfaceParams

end Custom