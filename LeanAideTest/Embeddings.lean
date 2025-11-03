import LeanAide.PromptBuilder
import LeanCodePrompts.Translate
namespace LeanAide
open Lean

-- #eval callSimilaritySearch "There are infinitely many odd primes" "docString" 5

def promptPairs : TranslateM (Array (String × Json)) := do
  let pb := PromptExampleBuilder.similarBuilder 3 0 0
  pb.getPromptPairs "There are infinitely many odd primes"

/--
info: #[("Infinite set variant of `Nat.exists_infinite_pseudoprimes`\n",
   "{\"type\": \"∀ {b : ℕ}, 1 ≤ b → {n : ℕ | n.FermatPsp b}.Infinite\",\n \"statement\":\n \"theorem Nat.infinite_setOf_pseudoprimes : ∀ {b : ℕ}, 1 ≤ b → {n | n.FermatPsp b}.Infinite := by sorry\",\n \"name\": \"Nat.infinite_setOf_pseudoprimes\",\n \"isProp\": true,\n \"isNoncomputable\": false,\n \"docString\": \"Infinite set variant of `Nat.exists_infinite_pseudoprimes`\\n\",\n \"distance\": 0.4534853398799896}"),
  ("There exists infinitely many deficient numbers ",
   "{\"type\": \"{n : ℕ | n.Deficient}.Infinite\",\n \"statement\":\n \"theorem Nat.infinite_deficient : {n | n.Deficient}.Infinite := by sorry\",\n \"name\": \"Nat.infinite_deficient\",\n \"isProp\": true,\n \"isNoncomputable\": false,\n \"docString\": \"There exists infinitely many deficient numbers \",\n \"distance\": 0.4458142817020416}"),
  ("For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. ",
   "{\"type\": \"∀ {k : ℕ}, k ≠ 0 → {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD k]}.Infinite\",\n \"statement\":\n \"theorem Nat.infinite_setOf_prime_modEq_one : ∀ {k : ℕ}, k ≠ 0 → {p | Nat.Prime p ∧ p ≡ 1 [MOD k]}.Infinite := by sorry\",\n \"name\": \"Nat.infinite_setOf_prime_modEq_one\",\n \"isProp\": true,\n \"isNoncomputable\": false,\n \"docString\":\n \"For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. \",\n \"distance\": 0.38997554779052734}")]
-/
#guard_msgs in
#eval promptPairs

/--
info: #[("Translate the following statement into Lean 4:\n## Theorem: There are infinitely many odd primes\n\nGive ONLY the Lean code",
   "{\"dummy\": 3}")]
-/
#guard_msgs in
#eval translatePromptPairs #[("There are infinitely many odd primes", json%{"dummy" : 3})]

def messagesPair : TranslateM Json := do
  let (messages, _) ←  Translator.getMessages "There are infinitely many odd primes" {params := {n := 3}, pb := .similarBuilder 3 0 0}
  return messages

/--
info: "[{\"role\": \"system\",\n  \"content\":\n  \"You are a Mathematics, Lean 4 and coding assistant who answers questions about Mathematics and Lean 4, gives hints while coding in Lean 4. You also translates from natural language to Lean Theorem Prover code and vice versa when asked. Follow EXACTLY any examples given when generating Lean code.\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: Infinite set variant of `Nat.exists_infinite_pseudoprimes`\\n\\n\\nGive ONLY the Lean code\"},\n {\"role\": \"assistant\",\n  \"content\": \"∀ {b : ℕ}, 1 ≤ b → {n : ℕ | n.FermatPsp b}.Infinite\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: There exists infinitely many deficient numbers \\n\\nGive ONLY the Lean code\"},\n {\"role\": \"assistant\", \"content\": \"{n : ℕ | n.Deficient}.Infinite\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. \\n\\nGive ONLY the Lean code\"},\n {\"role\": \"assistant\",\n  \"content\":\n  \"∀ {k : ℕ}, k ≠ 0 → {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD k]}.Infinite\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: There are infinitely many odd primes\\n\\nGive ONLY the Lean code\"}]"
-/
#guard_msgs in
#eval messagesPair


def messagesPairSysless : TranslateM Json := do
  let (messages, _) ←  Translator.getMessages "There are infinitely many odd primes" {params := {n := 3}, pb := .similarBuilder 3 0 0, server := .openAI (model := "o4-mini")}
  return messages

/--
info: "[{\"role\": \"user\",\n  \"content\":\n  \"You are a Mathematics, Lean 4 and coding assistant who answers questions about Mathematics and Lean 4, gives hints while coding in Lean 4. You also translates from natural language to Lean Theorem Prover code and vice versa when asked. Follow EXACTLY any examples given when generating Lean code.\"},\n {\"role\": \"assistant\",\n  \"content\":\n  \"Sure. I will answer precisely and concisely following instructions\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: Infinite set variant of `Nat.exists_infinite_pseudoprimes`\\n\\n\\nGive ONLY the Lean code\"},\n {\"role\": \"assistant\",\n  \"content\": \"∀ {b : ℕ}, 1 ≤ b → {n : ℕ | n.FermatPsp b}.Infinite\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: There exists infinitely many deficient numbers \\n\\nGive ONLY the Lean code\"},\n {\"role\": \"assistant\", \"content\": \"{n : ℕ | n.Deficient}.Infinite\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. \\n\\nGive ONLY the Lean code\"},\n {\"role\": \"assistant\",\n  \"content\":\n  \"∀ {k : ℕ}, k ≠ 0 → {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD k]}.Infinite\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: There are infinitely many odd primes\\n\\nGive ONLY the Lean code\"}]"
-/
#guard_msgs in
#eval messagesPairSysless


def messagesPairChatDetailedDoc : TranslateM Json := do
  let (messages, _) ←  Translator.getMessages "There are infinitely many odd primes" {params := {n := 3}, pb := .similarBuilder 3 0 0, toChat := .detailedDoc}
  return messages

/--
info: "[{\"role\": \"system\",\n  \"content\":\n  \"You are a Mathematics, Lean 4 and coding assistant who answers questions about Mathematics and Lean 4, gives hints while coding in Lean 4. You also translates from natural language to Lean Theorem Prover code and vice versa when asked. Follow EXACTLY any examples given when generating Lean code.\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Consider the mathematical theorem.\\n**Theorem:**\\nTranslate the following statement into Lean 4:\\n## Theorem: Infinite set variant of `Nat.exists_infinite_pseudoprimes`\\n\\n\\nGive ONLY the Lean code\\n---\\nTranslate the above mathematical statement into a Lean 4 `theorem` with name **Nat.infinite_setOf_pseudoprimes** with proof `by sorry`. Give the Lean code only\"},\n {\"role\": \"assistant\",\n  \"content\":\n  \"theorem Nat.infinite_setOf_pseudoprimes : ∀ {b : ℕ}, 1 ≤ b → Set.Infinite {n : ℕ | Nat.FermatPsp n b} := by sorry\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Consider the mathematical theorem.\\n**Theorem:**\\nTranslate the following statement into Lean 4:\\n## Theorem: There exists infinitely many deficient numbers \\n\\nGive ONLY the Lean code\\n---\\nTranslate the above mathematical statement into a Lean 4 `theorem` with name **Nat.infinite_deficient** with proof `by sorry`. Give the Lean code only\"},\n {\"role\": \"assistant\",\n  \"content\":\n  \"theorem Nat.infinite_deficient : Set.Infinite {n : ℕ | Nat.Deficient n} := by sorry\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Consider the mathematical theorem.\\n**Theorem:**\\nTranslate the following statement into Lean 4:\\n## Theorem: For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. \\n\\nGive ONLY the Lean code\\n---\\nTranslate the above mathematical statement into a Lean 4 `theorem` with name **Nat.infinite_setOf_prime_modEq_one** with proof `by sorry`. Give the Lean code only\"},\n {\"role\": \"assistant\",\n  \"content\":\n  \"theorem Nat.infinite_setOf_prime_modEq_one : ∀ {k : ℕ}, k ≠ 0 → Set.Infinite {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD k]} := by sorry\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: There are infinitely many odd primes\\n\\nGive ONLY the Lean code\"}]"
-/
#guard_msgs in
#eval messagesPairChatDetailedDoc

def messagesPairChatDetailed : TranslateM Json := do
  let (messages, _) ←  Translator.getMessages "There are infinitely many odd primes" {params := {n := 3}, pb := .similarBuilder 3 0 0, toChat := .detailed}
  return messages

/--
info: "[{\"role\": \"system\",\n  \"content\":\n  \"You are a Mathematics, Lean 4 and coding assistant who answers questions about Mathematics and Lean 4, gives hints while coding in Lean 4. You also translates from natural language to Lean Theorem Prover code and vice versa when asked. Follow EXACTLY any examples given when generating Lean code.\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: Infinite set variant of `Nat.exists_infinite_pseudoprimes`\\n\\n\\nGive ONLY the Lean code\"},\n {\"role\": \"assistant\",\n  \"content\":\n  \"theorem Nat.infinite_setOf_pseudoprimes : ∀ {b : ℕ}, 1 ≤ b → Set.Infinite {n : ℕ | Nat.FermatPsp n b} := by sorry\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: There exists infinitely many deficient numbers \\n\\nGive ONLY the Lean code\"},\n {\"role\": \"assistant\",\n  \"content\":\n  \"theorem Nat.infinite_deficient : Set.Infinite {n : ℕ | Nat.Deficient n} := by sorry\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. \\n\\nGive ONLY the Lean code\"},\n {\"role\": \"assistant\",\n  \"content\":\n  \"theorem Nat.infinite_setOf_prime_modEq_one : ∀ {k : ℕ}, k ≠ 0 → Set.Infinite {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD k]} := by sorry\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: There are infinitely many odd primes\\n\\nGive ONLY the Lean code\"}]"
-/
#guard_msgs in
#eval messagesPairChatDetailed


def messagesPairNoWrap : TranslateM Json := do
  let (messages, _) ←  Translator.getMessages "There are infinitely many odd primes" {params := {n := 3}, pb := .similarBuilder 3 0 0} (useInstructions := false)
  return messages

/--
info: "[{\"role\": \"system\",\n  \"content\":\n  \"You are a Mathematics, Lean 4 and coding assistant who answers questions about Mathematics and Lean 4, gives hints while coding in Lean 4. You also translates from natural language to Lean Theorem Prover code and vice versa when asked. Follow EXACTLY any examples given when generating Lean code.\"},\n {\"role\": \"user\",\n  \"content\": \"Infinite set variant of `Nat.exists_infinite_pseudoprimes`\\n\"},\n {\"role\": \"assistant\",\n  \"content\": \"∀ {b : ℕ}, 1 ≤ b → {n : ℕ | n.FermatPsp b}.Infinite\"},\n {\"role\": \"user\", \"content\": \"There exists infinitely many deficient numbers \"},\n {\"role\": \"assistant\", \"content\": \"{n : ℕ | n.Deficient}.Infinite\"},\n {\"role\": \"user\",\n  \"content\":\n  \"For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. \"},\n {\"role\": \"assistant\",\n  \"content\":\n  \"∀ {k : ℕ}, k ≠ 0 → {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD k]}.Infinite\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: There are infinitely many odd primes\\n\\nGive ONLY the Lean code\"}]"
-/
#guard_msgs in
#eval messagesPairNoWrap

def messagesPairDirect : TranslateM Json := do
  let (messages, _) ←  Translator.getMessages "There are infinitely many odd primes" {params := {n := 3}, pb := .similarBuilder 3 0 0, messageBuilder := MessageBuilder.directBuilder} (useInstructions := false)
  return messages

/--
info: "[{\"role\": \"user\",\n  \"content\":\n  \"You are a coding assistant who translates from natural language to Lean Theorem Prover code following examples. Follow EXACTLY the examples given.\\n\\nThe following are some examples of statements and their translations:\\n\\n## Natural language statement\\n\\nInfinite set variant of `Nat.exists_infinite_pseudoprimes`\\n\\n\\n## Lean Code\\n\\n∀ {b : ℕ}, 1 ≤ b → {n : ℕ | n.FermatPsp b}.Infinite\\n\\n## Natural language statement\\n\\nThere exists infinitely many deficient numbers \\n\\n## Lean Code\\n\\n{n : ℕ | n.Deficient}.Infinite\\n\\n## Natural language statement\\n\\nFor any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. \\n\\n## Lean Code\\n\\n∀ {k : ℕ}, k ≠ 0 → {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD k]}.Infinite\\n\\n---\\n\\nTranslate the following statement into Lean 4:\\n## Theorem: There are infinitely many odd primes\\n\\nGive ONLY the Lean code\"}]"
-/
#guard_msgs in
#eval messagesPairDirect

def messagesPairDirectDetailed : TranslateM Json := do
  let (messages, _) ←  Translator.getMessages "There are infinitely many odd primes" {params := {n := 3}, pb := .similarBuilder 3 0 0, messageBuilder := MessageBuilder.directBuilder, toChat := .detailed} (useInstructions := false)
  return messages

/--
info: "[{\"role\": \"user\",\n  \"content\":\n  \"You are a coding assistant who translates from natural language to Lean Theorem Prover code following examples. Follow EXACTLY the examples given.\\n\\nThe following are some examples of statements and their translations:\\n\\n## Natural language statement\\n\\nInfinite set variant of `Nat.exists_infinite_pseudoprimes`\\n\\n\\n## Lean Code\\n\\ntheorem Nat.infinite_setOf_pseudoprimes : ∀ {b : ℕ}, 1 ≤ b → Set.Infinite {n : ℕ | Nat.FermatPsp n b} := by sorry\\n\\n## Natural language statement\\n\\nThere exists infinitely many deficient numbers \\n\\n## Lean Code\\n\\ntheorem Nat.infinite_deficient : Set.Infinite {n : ℕ | Nat.Deficient n} := by sorry\\n\\n## Natural language statement\\n\\nFor any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. \\n\\n## Lean Code\\n\\ntheorem Nat.infinite_setOf_prime_modEq_one : ∀ {k : ℕ}, k ≠ 0 → Set.Infinite {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD k]} := by sorry\\n\\n---\\n\\nTranslate the following statement into Lean 4:\\n## Theorem: There are infinitely many odd primes\\n\\nGive ONLY the Lean code\"}]"
-/
#guard_msgs in
#eval messagesPairDirectDetailed

def messagesPairMin : TranslateM Json := do
  let (messages, _) ←  Translator.getMessages "There are infinitely many odd primes" {params := {n := 3}, pb := .similarBuilder 3 0 0, useInstructions := false}
  return messages

/--
info: "[{\"role\": \"system\",\n  \"content\":\n  \"You are a Mathematics, Lean 4 and coding assistant who answers questions about Mathematics and Lean 4, gives hints while coding in Lean 4. You also translates from natural language to Lean Theorem Prover code and vice versa when asked. Follow EXACTLY any examples given when generating Lean code.\"},\n {\"role\": \"user\",\n  \"content\": \"Infinite set variant of `Nat.exists_infinite_pseudoprimes`\\n\"},\n {\"role\": \"assistant\",\n  \"content\": \"∀ {b : ℕ}, 1 ≤ b → {n : ℕ | n.FermatPsp b}.Infinite\"},\n {\"role\": \"user\", \"content\": \"There exists infinitely many deficient numbers \"},\n {\"role\": \"assistant\", \"content\": \"{n : ℕ | n.Deficient}.Infinite\"},\n {\"role\": \"user\",\n  \"content\":\n  \"For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. \"},\n {\"role\": \"assistant\",\n  \"content\":\n  \"∀ {k : ℕ}, k ≠ 0 → {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD k]}.Infinite\"},\n {\"role\": \"user\",\n  \"content\":\n  \"Translate the following statement into Lean 4:\\n## Theorem: There are infinitely many odd primes\\n\\nGive ONLY the Lean code\"}]"
-/
#guard_msgs in
#eval messagesPairMin

end LeanAide
