import CodeAction.Interface
import StatementAutoformalisation.Config.Custom
import StatementAutoformalisation.Config.Informalisation
import StatementAutoformalisation.Config.SuggestName
-- import Mathbin.All

/-!
The code actions implemented so far can be tested here.

- To test autoformalisation, click anywhere on the comment below and 
  select the code action to translate it to Lean code.
- To test informalisation, click anywhere on the `example` below (EXCEPT 
  the end) and attempt to generate a natural language description.
- To test name suggestions, select the *type* of the `example` below
  (everything between `example` and `:=`, including the first `:`) and 
  attempt to generate a name for the declaration.
-/

/- Every prime number is either `2` or odd. -/

example : ∀ n : Nat, ∃ m : Nat, m > n ∧ m % 2 = 1  := sorry