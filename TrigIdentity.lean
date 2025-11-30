import LeanAideCore
import LeanAideCore.Syntax
import Lean
import Mathlib

open LeanAide Lean Meta Elab Parser Tactic
set_option linter.unusedTactic false
set_option linter.unusedVariables false

#leanaide_connect

open scoped Nat

def trigIdentityExample : Json :=
  json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "header": "Theorem",
        "label": "thm:cosine-product-to-sum",
        "hypothesis": [
          {
            "type": "assume_statement",
            "assumption": "x and y are real numbers."
          }
        ],
        "claim": "cos x cos y = 1/2 (cos(x+y) + cos(x-y))",
        "proof": [
          {
            "type": "assert_statement",
            "claim": "cos(x+y) = cos x cos y - sin x sin y",
            "proof_method": "cosine addition formula"
          },
          {
            "type": "assert_statement",
            "claim": "cos(x-y) = cos x cos y + sin x sin y",
            "proof_method": "cosine subtraction formula"
          },
          {
            "type": "assert_statement",
            "claim": "cos(x+y) + cos(x-y) = (cos x cos y - sin x sin y) + (cos x cos y + sin x sin y)",
            "proof_method": "Add the two identities termwise"
          },
          {
            "type": "assert_statement",
            "claim": "(cos x cos y - sin x sin y) + (cos x cos y + sin x sin y) = (cos x cos y + cos x cos y) + (- sin x sin y + sin x sin y)",
            "proof_method": "Group like terms"
          },
          {
            "type": "calculation",
            "calculation_sequence": [
              "cos x cos y + cos x cos y = 2 cos x cos y",
              "- sin x sin y + sin x sin y = 0"
            ]
          },
          {
            "type": "assert_statement",
            "claim": "cos(x+y) + cos(x-y) = 2 cos x cos y",
            "proof_method": "Simplify the grouped sums"
          },
          {
            "type": "assert_statement",
            "claim": "(cos(x+y) + cos(x-y)) / 2 = cos x cos y",
            "proof_method": "Divide both sides by 2"
          },
          {
            "type": "conclude_statement",
            "claim": "cos x cos y = 1/2 (cos(x+y) + cos(x-y))"
          }
        ]
      }
    ]
  }
}
