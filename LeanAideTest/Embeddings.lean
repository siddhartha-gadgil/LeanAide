import LeanAide.PromptBuilder
import LeanCodePrompts.Translate
namespace LeanAide
open Lean

-- #eval callSimilaritySearch "There are infinitely many odd primes" "docString" 5

def messagesPair : TranslateM Json := do
  let (messages, _) ←  Translator.getMessages "There are infinitely many odd primes" {params := {n := 3}, pb := .similarBuilder 3 0 0}
  return messages

/--
info: "[{\"role\": \"system\",\n  \"content\":\n  \"You are a Mathematics, Lean 4 and coding assistant who answers questions about Mathematics and Lean 4, gives hints while coding in Lean 4. You also translates from natural language to Lean Theorem Prover code and vice versa when asked. Follow EXACTLY any examples given when generating Lean code.\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: Infinite set variant of `Nat.exists_infinite_pseudoprimes`\\n\\n\\nGive ONLY the Lean code\"},\n {\"role\": \"assistant\",\n  \"content\": \"∀ {b : ℕ}, 1 ≤ b → {n : ℕ | n.FermatPsp b}.Infinite\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: There exists infinitely many deficient numbers \\n\\nGive ONLY the Lean code\"},\n {\"role\": \"assistant\", \"content\": \"{n : ℕ | n.Deficient}.Infinite\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. \\n\\nGive ONLY the Lean code\"},\n {\"role\": \"assistant\",\n  \"content\":\n  \"∀ {k : ℕ}, k ≠ 0 → {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD k]}.Infinite\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: There are infinitely many odd primes\\n\\nGive ONLY the Lean code\"}]"
-/
#guard_msgs in
#eval messagesPair


def messagesPair' : TranslateM Json := do
  let (messages, _) ←  Translator.getMessages "There are infinitely many odd primes" {params := {n := 3}, pb := .similarBuilder 3 0 0, server := .openAI (model := "o4-mini")}
  return messages

/--
info: "[{\"role\": \"user\",\n  \"content\":\n  \"You are a Mathematics, Lean 4 and coding assistant who answers questions about Mathematics and Lean 4, gives hints while coding in Lean 4. You also translates from natural language to Lean Theorem Prover code and vice versa when asked. Follow EXACTLY any examples given when generating Lean code.\"},\n {\"role\": \"assistant\",\n  \"content\":\n  \"Sure. I will answer precisely and concisely following instructions\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: Infinite set variant of `Nat.exists_infinite_pseudoprimes`\\n\\n\\nGive ONLY the Lean code\"},\n {\"role\": \"assistant\",\n  \"content\": \"∀ {b : ℕ}, 1 ≤ b → {n : ℕ | n.FermatPsp b}.Infinite\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: There exists infinitely many deficient numbers \\n\\nGive ONLY the Lean code\"},\n {\"role\": \"assistant\", \"content\": \"{n : ℕ | n.Deficient}.Infinite\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. \\n\\nGive ONLY the Lean code\"},\n {\"role\": \"assistant\",\n  \"content\":\n  \"∀ {k : ℕ}, k ≠ 0 → {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD k]}.Infinite\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: There are infinitely many odd primes\\n\\nGive ONLY the Lean code\"}]"
-/
#guard_msgs in
#eval messagesPair'

end LeanAide
