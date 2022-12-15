import StatementAutoformalisation.Interface
import StatementAutoformalisation.Translate
import StatementAutoformalisation.Config.FixedPrompts

namespace SuggestName

def LLMParams : LLM.Params :=
{
  openAIModel := "code-davinci-002",
  temperature := 4,
  n := 5,
  maxTokens := 200,
  stopTokens := #["\n\n"]
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
  printDecl := { toString := fun d => s!"{DeclarationWithDocstring.printType.toString d}\nName: {d.name.getD "none"}" }
  mkSuffix := fun d => s!"{d}\nName:",
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

@[codeActionProvider] def Action := performCodeAction InterfaceParams

end SuggestName