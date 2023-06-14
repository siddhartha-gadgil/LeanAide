import CodeAction.Interface
import StatementAutoformalisation.Translate
import StatementAutoformalisation.Config.FixedPrompts

namespace SuggestName

def LLMParams : LLM.Params :=
{
  openAIModel := "gpt-3.5-turbo",
  temperature := 4,
  n := 5,
  maxTokens := 200,
  stopTokens := #["\n\n"],
  systemMessage := "Please suggest a suitable name for the given theorem written in Lean."
}

def PromptParams : Prompt.Params :=
{
  toLLMParams := LLMParams, 
  toSentenceSimilarityParams := #[], 
  toKeywordExtractionParams := #[],
  fixedPrompts := leanChatPrompts,
  useNames := #[],
  useModules := #[],
  useMainCtx? := false,
  printMessage := fun decl => #[mkMessage "user" decl.printType, mkMessage "assistant" (decl.name.getD "none")],
  mkSuffix := id,
  processCompletion := fun type name => s!"/-- -/ {name} {type}"
}

def InterfaceParams : Interface.Params DeclarationWithDocstring :=
{
  -- Use this code action by selecting the arguments and type of the declaration for which the name is to be generated.
  title := "Suggest a suitable name for the selected type.",
  useSelection? := true,
  extractText? := some,
  action := fun stmt =>
    Prompt.translate ⟨PromptParams, stmt⟩ >>= fun (_, suggestions) => return suggestions[0]!,
  postProcess := fun type decl => s!"{decl.name.getD ""} {type}"
}

@[code_action_provider] def Action := performCodeAction InterfaceParams

end SuggestName