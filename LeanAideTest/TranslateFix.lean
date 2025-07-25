import Mathlib
import LeanAide.Actor
import LeanAide.ReTranslate
import LeanAide.ReTranslators

open LeanAide Lean Meta Translate

def exCode := "∃ (G : Type) [inst : Group G], ∀ g : G, g * g = 1"

def server := ({} : Translator).server

-- #eval server.mathCompletions <| (existsFixPrompt? exCode).get!

#eval retranslateFromErrors #[.unparsed exCode "<dummy>" none]

#eval allRetranslatePrompts "∃ (G : Type) [inst : Group G], ∀ g : G, g * g = 1"
