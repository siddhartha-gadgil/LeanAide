import StatementAutoformalisation.Translate
import StatementAutoformalisation.Config.FixedPrompts

def LLMParams : LLM.Params :=
{
  openAIModel := "code-davinci-002",
  temperature := 2,
  n := 1,
  maxTokens := 200,
  stopTokens := #["\n\n"]
}

def SentenceSimilarityParams : SentenceSimilarity.Params :=
{
  source := "data/safe-prompts.json",
  sentenceTransformersModel := "all-mpnet-base-v2",
  kind := "theorem",
  field := "doc_string",
  nSim := 0
}

def KeywordExtractionParams : KeywordExtraction.Params :=
{
  nKw := 0
}

def PromptParams : Prompt.Params :=
{
  LLMParams, 
  SentenceSimilarityParams, 
  KeywordExtractionParams with
  fixedPrompts := leanChatPrompts,
  useNames := #[],
  useModules := #[],
  useMainCtx? := false,
  printDecl := { toString := fun ⟨decl, docstring⟩ => s!"{toString decl}\n{printAsComment docstring}" }
  mkSuffix := fun stmt => s!"{stmt}\n/--",
  processCompletion := id
}