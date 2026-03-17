import LeanAideCore.Syntax
import LeanAideCore
import LeanAideCore.Responses
namespace LeanAide

open Meta

/--
## Testing Quote Command

This is the basic form of the quote command syntax
-/
#quote test_quote

#eval test_quote -- "## Testing Quote Command\n\nThis is the basic form of the quote command syntax"

/--
Quote command *without* identifier
-/
#quote

/--
# General quote command

We can apply any function with domain `String`, for example the constructor of a type.
-/
#quote fn_test <| fun s ↦ "Hello, world!\n" ++ s ;

#eval fn_test

-- Generation
open LeanAide.Discussion


-- #eval generateM "There are infinitely many odd numbers." Document

/-- There are infinitely many odd numbers. -/
#theorem_code infinitely_many_odd_numbers.theorem_code : {n | Odd n}.Infinite

#eval infinitely_many_odd_numbers.theorem_code




#start_chat chatEg

def chatEg₂ := chatEg.mkQuery  {message := "There are infinitely many even numbers."}

#prove chatEg₂ >> Response


#ask "Prove that there are infinitely many odd numbers" << chatEg

/--
Prove that there are infinitely many odd numnbers.
-/
#ask << chatEg

def chatEg₁ := chatEg + (thmText  "There are infinitely many odd numbers.")

#eval chatEg₁

#prove "There are infinitely many odd numbers." >> ProofDocument

namespace long_eg

/-- There are infinitely many odd numbers. -/
#theorem_code infinitely_many_odd_numbers.theorem_code : {n | Odd n}.Infinite

def infinitely_many_odd_numbers.theorem_code.chat :=
  LeanAide.Discussion.append chatEg₁ infinitely_many_odd_numbers.theorem_code

/-- ### Proof

Assume the set \( S = \{ n : \mathbb{N} \mid \text{Odd } n \} \). We aim to prove that the set \( S \) is infinite.

To do this, we will show the contrapositive: if \( S \) is finite, it leads to a contradiction. Assume for contradiction that \( S \) is finite. By the definition of a set being finite, there exists a natural number \( N \) such that \( S \subseteq \{ 0, 1, 2, \ldots, N \} \).

However, we will construct an element of \( S \) that is not in \( \{ 0, 1, 2, \ldots, N \} \) as follows. Let \( n_0 \) be the maximum element of \( S \) if it is non-empty; otherwise, let \( n_0 = 1 \). Consider the natural number \( m = n_0 + 2 \).

Since \( n_0 \) is an element of \( S \), by the definition of the set of odd numbers, there exists an integer \( k_0 \) such that \( n_0 = 2k_0 + 1 \). We define \( m = 2(k_0 + 1) + 1 \). By constructing \( m \) in this manner, we ensure \( m = 2(k_0 + 1) + 1 = 2k_1 + 1 \) for some integer \( k_1 = k_0 + 1 \).

Therefore, by the definition of odd numbers, \( m \) is an odd number. Thus, \( m \) is an element of \( S \), while \( m \) is strictly greater than \( N \) because \( m = n_0 + 2 \geq N + 1 \). This contradicts the assumption that \( S \) is finite and is contained in \( \{ 0, 1, 2, \ldots, N \} \).

Hence, the assumption that \( S \) is finite must be false. Therefore, the set \( S \) is infinite, as desired. -/
#proof_document infinitely_many_odd_numbers.proof_doc

def infinitely_many_odd_numbers.struct_proof : LeanAide.StructuredProof :=
  ⟨`infinitely_many_odd_numbers,
    json%
      {"document":
        {"type": "document", "title": "Proof of Infinitude of Odd Numbers", "body":
          [{"type": "assume_statement", "assumption":
              "n ∈ ℕ is an element of a semiring, and ℕ = {0, 1, 2, ...}."},
            {"type": "Theorem", "proof":
              {"type": "ProofDetails", "proof_steps":
                [{"variable_type": "element of ℕ", "variable_name": "a", "type": "let_statement",
                    "statement": "Let a be an arbitrary element in ℕ."},
                  {"variable_name": "k", "variable_kind": "element of ℕ", "type": "some_statement",
                    "statement": "The number a is even if there exists a k ∈ ℕ such that a = 2k."},
                  {"variable_name": "k", "variable_kind": "element of ℕ", "type": "some_statement",
                    "statement":
                    "The number a is odd if there exists a k ∈ ℕ such that a = 2k + 1."},
                  {"type": "assert_statement", "claim":
                    "For any a ∈ ℕ, one of the representations a = 2k or a = 2k + 1 must hold, making a either even or odd, but not both."}]},
              "label": "lem:odd_even", "header": "Lemma", "claim":
              "Every natural number is either odd or even."},
            {"type": "Theorem", "proof":
              {"type": "ProofDetails", "proof_steps":
                [{"type": "assume_statement", "assumption":
                    "n is an element of a semiring and n is odd."},
                  {"variable_name": "k", "variable_kind": "element of ℕ", "type": "some_statement",
                    "statement":
                    "By the definition of an odd number, there exists k ∈ ℕ such that n = 2k + 1."},
                  {"type": "calculation", "calculation_sequence":
                    ["n + 2 = 2k + 1 + 2", "n + 2 = 2(k + 1) + 1"]},
                  {"type": "assert_statement", "claim":
                    "n + 2 is also odd, as it can be expressed in the form 2m + 1 where m = k + 1."}]},
              "label": "lem:odd_plus_two", "header": "Lemma", "claim":
              "If n is odd, then n + 2 is also odd."},
            {"type": "Paragraph", "text":
              "Main Proof:\n\nWe aim to show that the set S = { n ∈ ℕ | Odd n } is infinite."},
            {"type": "assert_statement", "proof_method": "Direct proof", "claim":
              "Choose an odd starting point.", "calculation":
              {"type": "calculation", "inline_calculation":
                "n_0 = 1. By definition, n_0 is odd because 1 = 2 × 0 + 1."}},
            {"variable_type": "sequence of odd numbers", "variable_name": "sequence (n_i)", "type":
              "let_statement", "statement":
              "Define a sequence of odd numbers (n_i) by n_{i+1} = n_i + 2 for each i ≥ 0."},
            {"type": "assert_statement", "proof_method": "Deduction from Lemma",
              "internal_references": [{"target_identifier": "lem:odd_plus_two"}], "claim":
              "Show that each element in the sequence is odd."},
            {"type": "assert_statement", "statement":
              "Let n_i and n_j be two elements of the sequence, with i < j. Then n_j = n_i + 2(j-i), and since 2(j-i) > 0, we have n_j > n_i. Thus, the sequence is strictly increasing.",
              "proof_method": "Direct proof", "claim":
              "The sequence is injective and has no upper bound."},
            {"type": "conclude_statement", "claim":
              "The set of odd numbers in ℕ is infinite as there is no maximum element. For every N ∈ ℕ, there exists an i such that n_i > N."}]}}⟩

def infinitely_many_odd_numbers.proof_doc.chat :=
  LeanAide.Discussion.append infinitely_many_odd_numbers.theorem_code.chat infinitely_many_odd_numbers.proof_doc

def infinitely_many_odd_numbers'.struct_proof : LeanAide.StructuredProof :=
  ⟨`infinitely_many_odd_numbers,
    json%
      {"type": "object", "title": "Mathematical Document Wrapper", "required": ["document"],
        "properties":
        {"document":
          {"type": "object", "required": ["type", "body"], "properties":
            {"type":
              {"type": "string", "description": "The type of this document element.", "const":
                "document"},
              "body":
              {"items":
                [{"type": "Proof", "proof_steps":
                    {"type": "array", "items":
                      [{"type": "assume_statement", "assumption":
                          "The set \\( S = \\{ n : \\mathbb{N} \\mid \\text{Odd } n \\} \\)."},
                        {"type": "assume_statement", "assumption":
                          "Assume for contradiction that \\( S \\) is finite."},
                        {"variable_type": "natural number", "variable_name": "N", "type":
                          "let_statement", "statement":
                          "There exists a natural number \\( N \\) such that \\( S \\subseteq \\{ 0, 1, 2, \\ldots, N \\} \\)."},
                        {"variable_name": "n_0", "type": "let_statement", "statement":
                          "Let \\( n_0 \\) be the maximum element of \\( S \\) if it is non-empty; otherwise, let \\( n_0 = 1 \\)."},
                        {"variable_name": "m", "type": "let_statement", "statement":
                          "Consider the natural number \\( m = n_0 + 2 \\)."},
                        {"variable_name": "k_0", "variable_kind": "integer", "type":
                          "some_statement", "statement":
                          "There exists an integer \\( k_0 \\) such that \\( n_0 = 2k_0 + 1 \\)."},
                        {"variable_name": "m", "value": "2(k_0 + 1) + 1", "type": "let_statement",
                          "statement": "Define \\( m = 2(k_0 + 1) + 1 \\)."},
                        {"type": "assert_statement", "claim":
                          "By the definition of odd numbers, \\( m \\) is an odd number."},
                        {"type": "assert_statement", "claim":
                          "\\( m \\) is an element of \\( S \\) and \\( m > N \\)."},
                        {"type": "contradiction_statement", "proof":
                          {"type": "array", "items":
                            [{"type": "assert_statement", "claim":
                                "\\( m \\) is strictly greater than \\( N \\), which contradicts the assumption \\( S \\subseteq \\{ 0, 1, 2, \\ldots, N \\} \\)."}]},
                          "assumption": "S is finite"},
                        {"type": "conclude_statement", "claim": "The set \\( S \\) is infinite."}]},
                    "claim_label": "<anonymous>"}],
                "$ref": "#/$defs/LogicalStepSequence"}},
            "description":
            "The root of the mathematical document, containing a sequence of environments.",
            "additionalProperties": false}},
        "description": "JSON schema for a structured mathematical document.",
        "additionalProperties": false, "$schema": "https://json-schema.org/draft/2020-12/schema"}⟩

end long_eg

section product_consecutive_integers

def nat.mul_succ_even_induction.struct_proof : LeanAide.StructuredProof :=
  ⟨`nat.mul_succ_even_induction,
    json%
      {"document":
        {"type": "document", "body":
          [{"type": "assume_statement", "assumption": "n is a natural number, where n ∈ ℕ."},
            {"type": "assert_statement", "label": "main-assertion", "claim": "Even(n × (n + 1))"},
            {"type": "Definition", "name": "Even", "label": "def:even", "header": "Definition",
              "definition":
              "A number a is Even if there exists some element r such that a = r + r."},
            {"variable_type": "natural number", "variable_name": "a", "type": "let_statement",
              "statement": "Let a = n × (n + 1)."},
            {"type": "condition_cases_proof", "true_case_proof":
              {"type": "calculation", "calculation_sequence":
                ["n × (n + 1) = n^2 + n", "n^2 + n = n^2 + n = n^2 + n/1"]},
              "false_case_proof":
              {"type": "conclude_statement", "claim":
                "This case does not occur since it cannot be false that n × (n + 1) is not an even number."},
              "condition": "n × (n + 1) is an even number"},
            {"variable_type": "natural number", "variable_name": "r", "type": "let_statement",
              "statement": "Define r = (n × (n + 1)) / 2.", "properties":
              "Since n and n+1 are consecutive integers, one is even, ensuring n × (n + 1) is divisible by 2."},
            {"type": "condition_case", "proof":
              {"type": "calculation", "calculation_sequence":
                ["n × (n + 1) = 2 × r", "2 × r = r + r"]},
              "condition": "n × (n + 1) is a multiple of 2"},
            {"type": "conclude_statement", "results_used":
              [{"target_identifier": "def:even", "statement": "Definition of Even"},
                {"target_identifier": "main-assertion", "statement":
                  "Assertion that n × (n + 1) is even"}],
              "claim": "n × (n + 1) is Even by definition. This completes the proof."}]}}⟩

def pfJson := json% {"document" : [{
          "Theorem" : {"claim": "The product of two consecutive natural numbers is even.",
          "proof" : [{"type": "assume_statement", "assumption": "n is a natural number, where n ∈ ℕ."},
            {"type": "assert_statement", "label": "main-assertion", "claim": "Even(n × (n + 1))"},
            {"type": "Definition", "name": "Even", "label": "def:even", "header": "Definition",
              "definition":
              "A number a is Even if there exists some element r such that a = r + r."},
            {"variable_type": "natural number", "variable_name": "a", "type": "let_statement",
              "statement": "Let a = n × (n + 1)."},
            {"type": "condition_cases_proof", "true_case_proof":
              {"type": "calculation", "calculation_sequence":
                ["n × (n + 1) = n^2 + n", "n^2 + n = n^2 + n = n^2 + n/1"]},
              "false_case_proof":
              {"type": "conclude_statement", "claim":
                "This case does not occur since it cannot be false that n × (n + 1) is not an even number."},
              "condition": "n × (n + 1) is an even number"},
            {"variable_type": "natural number", "variable_name": "r", "type": "let_statement",
              "statement": "Define r = (n × (n + 1)) / 2.", "properties":
              "Since n and n+1 are consecutive integers, one is even, ensuring n × (n + 1) is divisible by 2."},
            {"type": "condition_case", "proof":
              {"type": "calculation", "calculation_sequence":
                ["n × (n + 1) = 2 × r", "2 × r = r + r"]},
              "condition": "n × (n + 1) is a multiple of 2"},
            {"type": "conclude_statement", "results_used":
              [{"target_identifier": "def:even", "statement": "Definition of Even"},
                {"target_identifier": "main-assertion", "statement":
                  "Assertion that n × (n + 1) is even"}],
              "claim": "n × (n + 1) is Even by definition. This completes the proof."}]}}]}

#codegen pfJson

end product_consecutive_integers

end LeanAide
