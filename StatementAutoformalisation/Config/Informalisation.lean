import CodeAction.Interface
import StatementAutoformalisation.Translate
import StatementAutoformalisation.Config.FixedPrompts

namespace Informalisation

def LLMParams : LLM.Params :=
{
  openAIModel := "gpt-3.5-turbo",
  temperature := 2,
  n := 1,
  maxTokens := 200,
  stopTokens := #["-/", "\n\n"],
  systemMessage := 
  "You are a coding assistant who translates from Lean Theorem Prover code to natural language following examples.
   Follow EXACTLY the examples given."
}

def SentenceSimilarityParams : SentenceSimilarity.Params :=
{
  source := "data/safe-prompts.json",
  sentenceTransformersModel := "all-mpnet-base-v2",
  kind := "theorem",
  field := "doc_string",
  nSim := 0
}

def PromptParams : Prompt.Params :=
{
  toLLMParams := LLMParams, 
  toSentenceSimilarityParams := #[SentenceSimilarityParams],
  fixedPrompts := leanChatPrompts,
  useNames := #[],
  useModules := #[],
  useMainCtx? := false,
  printMessage := fun decl => #[mkMessage "user" decl.toDeclaration.toString, mkMessage "assistant" decl.docstring],
  mkSuffix := id,
  processCompletion := fun stmt completion => s!"{printAsComment completion}\n{stmt}"
}

def InterfaceParams : Interface.Params DeclarationWithDocstring :=
{
  title := "Describe declaration in natural language.",
  extractText? := pure,
  action := fun stmt =>
    Prompt.translate ⟨PromptParams, stmt⟩ >>= (fun (_, translations) => pure translations[0]!),
  postProcess := fun _ => DeclarationWithDocstring.toString
}

@[code_action_provider] def Action := performCodeAction InterfaceParams

end Informalisation