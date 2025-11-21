import LeanAideCore
import LeanAideCore.Syntax
import Lean
import Mathlib

open LeanAide Lean Meta Elab Parser Tactic
set_option linter.unusedTactic false
set_option linter.unusedVariables false

#leanaide_connect

open scoped Nat

def egIsomorphicToAbelian := json% {
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
          "assumption": "f : G ≃_{Grp} H is a group isomorphism."
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
      "variable_name": "f_hom",
      "variable_type": "G → H",
      "properties": "the underlying group homomorphism of f.",
      "statement": "Let f_hom : G → H denote the underlying group homomorphism of f."
    },
    {
      "type": "assert_statement",
      "claim": "f_hom is bijective."
    },
    {
      "type": "assert_statement",
      "claim": "f_hom satisfies ∀ g1, g2 : G, f_hom(g1 ·_G g2) = f_hom(g1) ·_H f_hom(g2)."
    },

    {
      "type": "Definition",
      "label": "def:phi_inv",
      "header": "Definition",
      "name" : "f_inv",
      "definition": "For all h : H, f_hom(f_inv(h)) = h and f_inv(f_hom(g)) = g."
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
              "value": "f_inv(x)",
              "statement": "Define g1 := f_inv(x)."
            },
            {
              "type": "let_statement",
              "variable_name": "g2",
              "value": "f_inv(y)",
              "statement": "Define g2 := f_inv(y)."
            },
            {
              "type": "assert_statement",
              "claim": "f_hom(g1) = x",
              "internal_references": [
                {
                  "target_identifier": "def:phi_hom"
                }
              ]
            },
            {
              "type": "assert_statement",
              "claim": "f_hom(g2) = y",
              "internal_references": [
                {
                  "target_identifier": "def:phi_hom"
                }
              ]
            },
            {
              "type": "assert_statement",
              "claim": "x ·_H y = f_hom(g1 ·_G g2)",
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
              "claim": "f_hom(g1 ·_G g2) = y ·_H x",
              "calculation": {
                "calculation_sequence": [
                  "f_hom(g1 ·_G g2) = f_hom(g2 ·_G g1)",
                  "f_hom(g2 ·_G g1) = f_hom(g2) ·_H f_hom(g1)",
                  "f_hom(g2) ·_H f_hom(g1) = y ·_H x"
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

theorem assert_7306146892611878405 :
    ∀ {G H : Type u} [inst_G : Group G] [inst_H : Group H] (f : G ≃* H),
      Function.Bijective (⇑f.toMonoidHom : G → H) :=
  by
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact fun {G H} [Group G] [Group H] f => MulEquiv.bijective f
theorem assert_4183249187002226786 :
    ∀ {G : Type u} [inst : Group G] {H : Type v} [inst_1 : Group H] (f : G →* H) (g1 g2 : G),
      (f : G → H) (g1 * g2) = (f : G → H) g1 * (f : G → H) g2 :=
  by
  simp only [map_mul, implies_true]

def f_hom_inv_properties {G H : Type*} [Group G] [Group H] (f : G ≃* H) :=
  let f_hom := f.toMonoidHom
  let f_inv := f.symm.toMonoidHom
  ∀ h : H, f_hom (f_inv h) = h ∧ ∀ g : G, f_inv (f_hom g) = g

theorem abelian_of_image_abelian :
    ∀ {G : Type u} [inst : Group G] {H : Type v} [inst_1 : CommGroup H] (f : G →* H) (x y : H),
      x * y = y * x :=
  by
  intro G inst H inst_1 f x y
  exact CommGroup.mul_comm x y
