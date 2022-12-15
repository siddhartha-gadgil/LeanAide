import StatementAutoformalisation.Interface
import StatementAutoformalisation.Config.Custom
import StatementAutoformalisation.Config.Informalisation
-- import Mathbin.All

/- Every natural number can be written as the sum of two squares. -/

def inf_odd_nat  : ∀ n : Nat, ∃ m : Nat, m > n ∧ m % 2 = 1  := sorry  