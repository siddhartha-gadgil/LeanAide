import LeanAideCore
import LeanAideCore.Syntax
import Mathlib
import Lean
import Qq

open LeanAide Lean Meta Elab Parser Tactic
set_option linter.unusedTactic false

open Nat

open Qq
#leanaide_connect "http://10.134.13.103:7654"

#eval LeanAidePipe.response <| json% {"task": "echo"}

-- universe u v w u_1 u_2 u_3 u₁ u₂ u₃
-- open scoped Nat
-- @[default_instance]
-- instance : Add ℤ := inferInstance
-- @[default_instance]
-- instance : Semiring ℤ := inferInstance


def egTheorem : Json :=
  json% {
    "type": "theorem",
    "name": "egTheorem",
    "claim_label": "egTheorem",
    "claim": "There are infinitely many odd numbers.",
    "proof": {
      "proof_steps": []
    }
  }



#codegen {
  "document": [
    {
      "type": "Theorem",
      "header": "Lemma",
      "label": "lem:inverse_one",
      "hypothesis": [
        {
          "type": "let_statement",
          "variable_name": "G",
          "variable_type": "Type u",
          "statement": "G : Type u"
        },
        {
          "type": "assume_statement",
          "assumption": "[Group G]"
        },
        {
          "type": "let_statement",
          "variable_name": "a",
          "variable_type": "G",
          "statement": "a : G"
        },
        {
          "type": "assume_statement",
          "assumption": "hâ‚ : a = 1"
        }
      ],
      "claim": "aâ»Â¹ = 1",
      "proof": {
        "type": "Proof",
        "claim_label": "lem:inverse_one",
        "proof_steps": [
          [
            {
              "type": "assert_statement",
              "label": "step1",
              "claim": "aâ»Â¹ = 1â»Â¹",
              "proof_method": "Eq.subst",
              "internal_references": [
                {
                  "target_identifier": "hâ‚"
                }
              ],
              "results_used": [
                {
                  "statement": "Eq.subst for inv",
                  "mathlib_identifier": "Eq.subst"
                }
              ]
            },
            {
              "type": "assert_statement",
              "label": "step2",
              "claim": "1â»Â¹ = 1",
              "proof_method": "inv_one",
              "internal_references": [
                {
                  "target_identifier": "inv_one"
                }
              ]
            },
            {
              "type": "assert_statement",
              "claim": "aâ»Â¹ = 1",
              "proof_method": "transitivity",
              "results_used": [
                {
                  "statement": "aâ»Â¹ = 1â»Â¹",
                  "target_identifier": "step1"
                },
                {
                  "statement": "1â»Â¹ = 1",
                  "target_identifier": "step2"
                }
              ]
            },
            {
              "type": "conclude_statement"
            }
          ]
        ]
      }
    },
    {
      "type": "Theorem",
      "header": "Theorem",
      "label": "thm:inverse_self",
      "hypothesis": [
        {
          "type": "let_statement",
          "variable_name": "G",
          "variable_type": "Type u",
          "statement": "G : Type u"
        },
        {
          "type": "assume_statement",
          "assumption": "[Group G]"
        },
        {
          "type": "let_statement",
          "variable_name": "e",
          "variable_type": "G",
          "statement": "e : G"
        },
        {
          "type": "assume_statement",
          "assumption": "hâ‚‚ : e = 1"
        }
      ],
      "claim": "eâ»Â¹ = e",
      "proof": {
        "type": "Proof",
        "claim_label": "thm:inverse_self",
        "proof_steps": [
          [
            {
              "type": "assert_statement",
              "label": "step1",
              "claim": "eâ»Â¹ = 1",
              "proof_method": "by Lemma 1",
              "internal_references": [
                {
                  "target_identifier": "lem:inverse_one"
                }
              ]
            },
            {
              "type": "assert_statement",
              "label": "step2",
              "claim": "1 = e",
              "proof_method": "Eq.symm",
              "internal_references": [
                {
                  "target_identifier": "hâ‚‚"
                }
              ]
            },
            {
              "type": "assert_statement",
              "claim": "eâ»Â¹ = e",
              "proof_method": "transitivity",
              "results_used": [
                {
                  "statement": "eâ»Â¹ = 1",
                  "target_identifier": "step1"
                },
                {
                  "statement": "1 = e",
                  "target_identifier": "step2"
                }
              ]
            },
            {
              "type": "conclude_statement"
            }
          ]
        ]
      }
    }
  ]
}
