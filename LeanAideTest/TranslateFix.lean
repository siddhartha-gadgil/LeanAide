import Mathlib
import LeanAide.Actor

open LeanAide Meta Translate

def exCode := "∃ (G : Type) [inst : Group G], ∀ g : G, g * g = 1"

def existsFixPrompt (exCode: String)  := s!"The following is **incorrect** Lean Prover code. The probable fix is: For an 'exists' statement, typeclasses should also use parenthesis not square brackets:
{exCode}
Fix the code and output ONLY the corrected code (NOT in a code block and with NO comments)."

def server := ({} : Translator).server

-- #eval server.mathCompletions <| existsFixPrompt exCode

#check ElabError
