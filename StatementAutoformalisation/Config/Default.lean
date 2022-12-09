import StatementAutoformalisation.Translate
import StatementAutoformalisation.Config.FixedPrompts

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
  mkSuffix := fun stmt => s!"{printAsComment stmt}\n{SentenceSimilarityParams.kind}",
  processCompletion := fun comment completion => s!"{printAsComment comment}\n{SentenceSimilarityParams.kind} {completion}"
}