import Mathlib
import LeanAide.Actor
import LeanAide.ReTranslate

open LeanAide Lean Meta Translate

def exCode := "∃ (G : Type) [inst : Group G], ∀ g : G, g * g = 1"

@[retranslate]
def existsFixPrompt? (exCode: String) : Option String  :=
  if exCode.contains '∃' && exCode.contains '[' then
    some <|
  s!"The following is **incorrect** Lean Prover code. The probable fix is: For an 'exists' statement, typeclasses should also use parenthesis not square brackets:
{exCode}
Fix the code and output ONLY the corrected code (NOT in a code block and with NO comments)."
  else
    none

def server := ({} : Translator).server

#eval server.mathCompletions <| (existsFixPrompt? exCode).get!

#eval retranslateFromStrings #[exCode]  ({} : Translator) 3

#eval allRetranslatePrompts "∃ (G : Type) [inst : Group G], ∀ g : G, g * g = 1"
