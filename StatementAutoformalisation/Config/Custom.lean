import StatementAutoformalisation.Translate
import StatementAutoformalisation.Config.FixedPrompts

def LLMParams : LLM.Params :=
{
  model := "code-davinci-002",
  temperature := 2,
  n := 1,
  maxTokens := 200,
  stopTokens := #[":=", "\n\n/-", "\n/-", "/-"]
}

def SentenceSimilarityParams : SentenceSimilarity.Params :=
{
  source := "data/safe-prompts.json",
  model := "all-mpnet-base-v2",
  kind := "theorem",
  field := "doc_string",
  nSim := 10
}

def KeywordExtractionParams : KeywordExtraction.Params :=
{
  nKw := 0
}

def CustomPromptParams : Prompt.Params :=
{
  LLMParams, 
  SentenceSimilarityParams, 
  KeywordExtractionParams with
  fixedPrompts := leanChatPrompts,
  useNames := #[],
  useModules := #[],
  useMainCtx? := false,
  printDecl := DeclarationWithDocstring.toString
  mkSuffix := fun stmt => s!"{printAsComment stmt}\n{SentenceSimilarityParams.kind}",
  processCompletion := id
}