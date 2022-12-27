import CodeAction.Interface
import StatementAutoformalisation.Translate
import StatementAutoformalisation.Config.FixedPrompts

namespace Informalisation

def LLMParams : LLM.Params :=
{
  openAIModel := "code-davinci-002",
  temperature := 2,
  n := 1,
  maxTokens := 200,
  stopTokens := #["-/", "\n\n"]
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

/-- The expected `kind` (`theorem`/`def`/...) of the completion.
  This variable is required only to modify the suffix of the main prompt. -/
def expectedKind? : Option String := none

def PromptParams : Prompt.Params :=
{
  toLLMParams := LLMParams, 
  toSentenceSimilarityParams := #[SentenceSimilarityParams], 
  toKeywordExtractionParams := #[KeywordExtractionParams],
  fixedPrompts := leanChatPrompts,
  useNames := #[],
  useModules := #[],
  useMainCtx? := false,
  printDecl := { toString := fun ⟨decl, docstring⟩ => s!"{toString decl}\n{printAsComment docstring}" }
  mkSuffix := fun stmt => s!"{stmt}\n/--",
  processCompletion := fun stmt completion => s!"{printAsComment completion}\n{stmt}"
}

def InterfaceParams : Interface.Params DeclarationWithDocstring :=
{
  title := "Describe declaration in natural language.",
  extractText? := pure,
  action := fun stmt =>
    Prompt.translate ⟨PromptParams, stmt⟩ >>= (fun (_, translations) => pure translations[0]!),
  postProcess := fun _ => DeclarationWithDocstring.toString.toString
}

@[codeActionProvider] def Action := performCodeAction InterfaceParams

end Informalisation