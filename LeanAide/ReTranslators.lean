import LeanAide.ReTranslate

namespace LeanAide

open Translator Lean Meta Elab Term Qq

-- @[retranslate]
-- def existsFixPrompt? (err: ElabError) : Option String  :=
--   let exCode := err.text
--   if exCode.contains '∃' && exCode.contains '[' then
--     some <|
--   s!"The following is **incorrect** Lean Prover code. The probable fix is: For an 'exists' statement, typeclasses should also use parenthesis not square brackets:
-- {exCode}
-- Fix the code and output ONLY the corrected code (NOT in a code block and with NO comments)."
--   else
--     none

@[retranslate]
def existsFixPrompt?' (exCode: String) : Option String  :=
  if exCode.contains '∃' && exCode.contains '[' then
    some <|
  s!"The following is **incorrect** Lean Prover code. The probable fix is: For an 'exists' statement, typeclasses should also use parenthesis not square brackets:
{exCode}
Fix the code and output ONLY the corrected code (NOT in a code block and with NO comments)."
  else
    none
