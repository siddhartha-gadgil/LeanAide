import LeanAide
import Lean
import Qq

open LeanAide Lean Meta Elab Parser Tactic
set_option linter.unusedTactic false

open Nat

def egIsomorphicToAbelian' := json% {
  "document": [
    {
      "type": "Section",
      "label": "sec:assumptions",
      "header": "Assumptions",
      "level": 1,
      "content": [
        {
          "type": "let_statement",
          "variable_name": "G",
          "variable_type": "type equipped with group structure (G, ·_G, e_G, inv_G)",
          "statement": "Let G be a type equipped with group structure (G, ·_G, e_G, inv_G)."
        },
        {
          "type": "let_statement",
          "variable_name": "H",
          "variable_type": "type equipped with group structure (H, ·_H, e_H, inv_H)",
          "statement": "Let H be a type equipped with group structure (H, ·_H, e_H, inv_H)."
        },
        {
          "type": "assume_statement",
          "assumption": "ϕ : G ≃_{Grp} H is a group isomorphism."
        },
        {
          "type": "assume_statement",
          "label": "h_comm",
          "assumption": "∀ g1 g2 : G, g1 ·_G g2 = g2 ·_G g1."
        }
      ]
    },
    {
      "type" : "let_statement",
      "label": "let:phi",
      "variable_name": "ϕ_hom",
      "variable_type": "G → H",
      "properties": "the underlying group homomorphism of ϕ.",
      "statement": "Let ϕ_hom : G → H denote the underlying group homomorphism of ϕ."
    },
    {
      "type": "assert_statement",
      "claim": "ϕ_hom is bijective."
    },
    {
      "type": "assert_statement",
      "claim": "ϕ_hom satisfies ∀ g1, g2 : G, ϕ_hom(g1 ·_G g2) = ϕ_hom(g1) ·_H ϕ_hom(g2)."
    },

    {
      "type": "Definition",
      "label": "def:phi_inv",
      "header": "Definition",
      "name" : "ϕ_inv",
      "definition": "For all h : H, ϕ_hom(ϕ_inv(h)) = h and ϕ_inv(ϕ_hom(g)) = g."
    },
    {
      "type": "Theorem",
      "label": "thm:H-abelian",
      "header": "Theorem",
      "claim": "∀ x y : H, x ·_H y = y ·_H x.",
      "proof": {
        "type": "Proof",
        "claim_label": "thm:H-abelian",
        "proof_steps": [
          [
            {
              "type": "let_statement",
              "variable_name": "x",
              "variable_type": "element of H",
              "statement": "Let x be an arbitrary element of H."
            },
            {
              "type": "let_statement",
              "variable_name": "y",
              "variable_type": "element of H",
              "statement": "Let y be an arbitrary element of H."
            },
            {
              "type": "let_statement",
              "variable_name": "g1",
              "value": "ϕ_inv(x)",
              "statement": "Define g1 := ϕ_inv(x)."
            },
            {
              "type": "let_statement",
              "variable_name": "g2",
              "value": "ϕ_inv(y)",
              "statement": "Define g2 := ϕ_inv(y)."
            },
            {
              "type": "assert_statement",
              "claim": "ϕ_hom(g1) = x",
              "internal_references": [
                {
                  "target_identifier": "def:phi_hom"
                }
              ]
            },
            {
              "type": "assert_statement",
              "claim": "ϕ_hom(g2) = y",
              "internal_references": [
                {
                  "target_identifier": "def:phi_hom"
                }
              ]
            },
            {
              "type": "assert_statement",
              "claim": "x ·_H y = ϕ_hom(g1 ·_G g2)",
              "internal_references": [
                {
                  "target_identifier": "def:phi_hom"
                }
              ]
            },
            {
              "type": "assert_statement",
              "claim": "g1 ·_G g2 = g2 ·_G g1",
              "internal_references": [
                {
                  "target_identifier": "h_comm"
                }
              ]
            },
            {
              "type": "assert_statement",
              "claim": "ϕ_hom(g1 ·_G g2) = y ·_H x",
              "calculation": {
                "calculation_sequence": [
                  "ϕ_hom(g1 ·_G g2) = ϕ_hom(g2 ·_G g1)",
                  "ϕ_hom(g2 ·_G g1) = ϕ_hom(g2) ·_H ϕ_hom(g1)",
                  "ϕ_hom(g2) ·_H ϕ_hom(g1) = y ·_H x"
                ]
              },
              "internal_references": [
                {
                  "target_identifier": "def:phi_hom"
                }
              ]
            },
            {
              "type": "conclude_statement",
              "claim": "Therefore, x ·_H y = y ·_H x."
            }
          ]
        ]
      }
    }
  ]
}

-- set_option maxHeartbeats 1000000 in
-- #codegen egIsomorphicToAbelian'
