import StatementAutoformalisation.Interface
import StatementAutoformalisation.Config.Informalisation
-- import Mathbin.All

def req : Prompt.Request := 
  ⟨PromptParams, "theorem xyz : ∀ n : ℕ, ∃ m : ℕ, m > n ∧ m % 2 = 1"⟩

#eval Prompt.translate req