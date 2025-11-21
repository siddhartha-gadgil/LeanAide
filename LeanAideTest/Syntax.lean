import LeanAideCore.Syntax
import LeanAideCore
import LeanAide.Responses
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

def infinitely_many_odd_numbers.proof_doc.chat :=
  LeanAide.Discussion.append infinitely_many_odd_numbers.theorem_code.chat infinitely_many_odd_numbers.proof_doc

def infinitely_many_odd_numbers.struct_proof : LeanAide.StructuredProof :=
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



end LeanAide
