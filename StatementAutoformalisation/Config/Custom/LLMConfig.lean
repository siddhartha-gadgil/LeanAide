import StatementAutoformalisation.LLMQuery

def CustomLLMParams : LLM.Params :=
{
  model := "code-davinci-002",
  temperature := 2,
  n := 1,
  maxTokens := 200,
  stopTokens := #[":=", "\n\n/-", "\n/-", "/-"]
}