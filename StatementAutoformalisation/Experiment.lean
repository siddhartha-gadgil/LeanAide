import StatementAutoformalisation.Interface
import StatementAutoformalisation.Config.Custom
import StatementAutoformalisation.Config.Informalisation
import StatementAutoformalisation.Config.SuggestName
-- import Mathbin.All

/- Every natural number can be written as the sum of two squares. -/

example : ∀ n : Nat, ∃ m : Nat, m > n ∧ m % 2 = 1  := sorry