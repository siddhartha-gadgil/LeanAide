import Mathlib
import LeanCodePrompts.Translate
import LeanCodePrompts.CodeAction
-- import LeanAide.CommentCodeAction

/-!
# Translation demo

To see translation in action, place the cursor anywhere on one of the comments below and invoke the code action to translate by clicking on the lightbulb or using `ctrl-.`. 
-/


//- There are infinitely many odd numbers -/

//- Every prime number is either `2` or odd -/

-- set_option trace.Translate.info true 
#eval translateViewM "There are infinitely many odd numbers"

#eval translateViewM "Every prime number is either `2` or odd"
