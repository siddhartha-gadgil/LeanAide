import CodeAction.Interface
import StatementAutoformalisation.Translate
import StatementAutoformalisation.Config.FixedPrompts

namespace Custom

def LLMParams : LLM.Params :=
{
  openAIModel := "gpt-3.5-turbo",
  temperature := 2,
  n := 1,
  maxTokens := 200,
  stopTokens := #[":=", "\n\n/-", "\n/-", "/-"]
  systemMessage := 
  "You are a coding assistant who translates from natural language to Lean Theorem Prover code following examples.
   Follow EXACTLY the examples given."
}

def SentenceSimilarityParams : SentenceSimilarity.Params :=
{
  source := "data/prompts.json",
  sentenceTransformersModel := "all-mpnet-base-v2",
  kind := "theorem",
  field := "doc_string",
  nSim := 10
}

def PromptParams : Prompt.Params :=
{
  toLLMParams := LLMParams, 
  toSentenceSimilarityParams := #[SentenceSimilarityParams],
  fixedPrompts := leanChatPrompts,
  useNames := #[],
  useModules := #[],
  useMainCtx? := false,
  printMessage := DeclarationWithDocstring.toMessage
  mkSuffix := id,
  processCompletion := fun comment completion => s!"{printAsComment comment}\n{completion}"
}

def InterfaceParams : Interface.Params DeclarationWithDocstring :=
{
  title := "Translate comment to Lean theorem statement (with custom settings).",
  nearestOccurrence? := nearestComment,
  extractText? := extractCommentText?,
  action := fun stmt =>
    Prompt.typecorrectTranslations ⟨PromptParams, stmt⟩ >>= (pure ·[0]!),
  postProcess := fun _ => DeclarationWithDocstring.toString
}

@[code_action_provider] def Action := performCodeAction InterfaceParams

end Custom