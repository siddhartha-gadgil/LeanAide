import StatementAutoformalisation.Interface
import StatementAutoformalisation.Config.Custom
-- import Mathbin.All

def req : Prompt.Request := 
  ⟨PromptParams, "A closed subset of a compact space is compact"⟩

-- #eval Prod.snd <$> Prompt.translate req