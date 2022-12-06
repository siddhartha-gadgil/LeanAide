import StatementAutoformalisation.Translate
import StatementAutoformalisation.Config.Custom.LLMConfig
import StatementAutoformalisation.Config.Custom.SentenceSimilarityConfig
import StatementAutoformalisation.Config.Custom.KeywordExtractionConfig
import StatementAutoformalisation.Config.Custom.FixedPrompts


def CustomPromptParams : Prompt.Params :=
{
  CustomLLMParams, 
  CustomSentenceSimilarityParams, 
  CustomKeywordExtractionParams with
  fixedPrompts := #[],
  useNames := #[],
  useModules := #[],
  useMainCtx? := false,
  printDecl := DeclarationWithDocstring.toString
}