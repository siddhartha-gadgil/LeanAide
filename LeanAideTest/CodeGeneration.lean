import LeanAide
import Lean
import Qq

open LeanAide Lean Meta Elab Parser Tactic
set_option linter.unusedTactic false

open Nat

open Qq

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

-- #codegen {
--     "type": "theorem",
--     "name": "egTheorem",
--     "claim_label": "egTheorem",
--     "claim": "There are infinitely many odd numbers.",
--     "proof": {
--       "proof_steps": []
--     }
--   }

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
          "assumption": "h₁ : a = 1"
        }
      ],
      "claim": "a⁻¹ = 1",
      "proof": {
        "type": "Proof",
        "claim_label": "lem:inverse_one",
        "proof_steps": [
          [
            {
              "type": "assert_statement",
              "label": "step1",
              "claim": "a⁻¹ = 1⁻¹",
              "proof_method": "Eq.subst",
              "internal_references": [
                {
                  "target_identifier": "h₁"
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
              "claim": "1⁻¹ = 1",
              "proof_method": "inv_one",
              "internal_references": [
                {
                  "target_identifier": "inv_one"
                }
              ]
            },
            {
              "type": "assert_statement",
              "claim": "a⁻¹ = 1",
              "proof_method": "transitivity",
              "results_used": [
                {
                  "statement": "a⁻¹ = 1⁻¹",
                  "target_identifier": "step1"
                },
                {
                  "statement": "1⁻¹ = 1",
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
          "assumption": "h₂ : e = 1"
        }
      ],
      "claim": "e⁻¹ = e",
      "proof": {
        "type": "Proof",
        "claim_label": "thm:inverse_self",
        "proof_steps": [
          [
            {
              "type": "assert_statement",
              "label": "step1",
              "claim": "e⁻¹ = 1",
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
                  "target_identifier": "h₂"
                }
              ]
            },
            {
              "type": "assert_statement",
              "claim": "e⁻¹ = e",
              "proof_method": "transitivity",
              "results_used": [
                {
                  "statement": "e⁻¹ = 1",
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


def egTheorem' : Json :=
  json% {
    "type": "theorem",
    "name": "egTheorem",
    "label": "egTheorem",
    "claim": "There are infinitely many odd numbers."
  }

def egTheorem.prop : Prop :=
  Set.Infinite {n : ℤ | Odd n}
def deferred.egTheorem [assume_egTheorem : Fact egTheorem.prop] : egTheorem.prop :=
  assume_egTheorem.elim

#codegen egTheorem'

def egTheorem'' : Json :=
  json% {
    "type": "theorem",
    "name": "egTheorem",
    "claim_label": "egTheorem",
    "claim": "There are infinitely many odd numbers.",
    "proof": {
      "proof_steps": []
    }
  }

def egLet : Json :=
  json% {
    "type" : "let_statement",
    "variable_name": "n",
    "variable_type": "natural number",
    "properties": "n is odd and n > 0"
  }

def egTheorem₀ : Json :=
  json% {
    "type": "theorem",
    "name": "egTheorem",
    "claim_label": "egTheorem",
    "claim": "Every natural number is less than its successor.",
    "proof": {
      "proof_steps": []
    }
  }

def egErrorProof : Json :=
  json% {"document" :
    [{
    "type": "theorem",
    "name": "egTheorem",
    "label": "egTheorem",
    "claim": "There are infinitely many odd numbers."
  },
      {"type": "proof",
    "claim_label": "egErrorProof",
    "proof_steps": []}]

  }

open Codegen

def showStx (source: Json) (cat: Name := ``commandSeq) (translator: CodeGenerator := {})(goal? : Option (MVarId) := none)
   :
    TranslateM (Format) := do
    match ← getCode translator  goal? cat source with
    | none => do
      return "No code generated"
    | some stx => do
      PrettyPrinter.ppCategory cat stx

#eval showStx egErrorProof

-- #eval showStx egTheorem₀

-- #eval showStx egTheorem

-- #eval showStx egTheorem''



-- #eval egTheorem


-- #eval showStx egLet

def egView : MetaM Format := do
  let .ok js := runParserCategory (← getEnv) `json egTheorem.pretty | throwError
    "Failed to parse egLet as JSON"
  PrettyPrinter.ppCategory `json js

#eval egView

def egTacs : TermElabM <|  Format := do
  let goal := q(∀ (N : ℤ), N % 10 = 0 ∨ N % 10 = 5 → 5 ∣ N)
  let autoTac ← `(tactic| aesop?)
  let tacs ← runTacticsAndGetTryThisI goal #[autoTac]
  PrettyPrinter.ppCategory ``tacticSeq <| ← `(tacticSeq|$tacs*)


#eval egTacs

/--
info: Try this:
  intro a
  simp_all only [EuclideanDomain.mod_eq_zero]
  cases a with
  | inl h => sorry
  | inr h_1 => sorry
---
warning: aesop: failed to prove the goal after exhaustive search.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example: ∀ (N : ℤ), N % 10 = 0 ∨ N % 10 = 5 → 5 ∣ N := by
  intro
  aesop?
  · sorry
  · sorry

#eval (ChatServer.default).fullStatement "p ∤ m!"

#eval Translator.translateToPropStrict "p ∤ m!" {}

example : 5 ∣ 10 := by
  hammer {aesopPremises := 5, autoPremises := 0}

theorem nat_lt_succ : ∀ (n : ℕ), n < succ n := by
    intro n
    trace "Automation tactics found for n < n.succ, closing goal"
    simp_all only [succ_eq_add_one, lt_add_iff_pos_right, lt_one_iff, pos_of_gt]

/-!
Definitions were replaced or modified. The original ones are:
```json
    {
      "type": "Definition",
      "label": "def:phi_hom",
      "header": "Definition",
      "definition": "Let φ_hom : G → H denote the underlying group homomorphism of φ. By definition of group isomorphism, φ_hom is bijective and satisfies ∀ g1, g2 : G, φ_hom(g1 ·_G g2) = φ_hom(g1) ·_H φ_hom(g2)."
    },
    {
      "type": "Definition",
      "label": "def:phi_inv",
      "header": "Definition",
      "definition": "Let φ_inv : H → G denote the inverse function of the bijection φ_hom. Then for all h : H, φ_hom(φ_inv(h)) = h and φ_inv(φ_hom(g)) = g."
    }
```

-/

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
          "assumption": "φ : G ≃_{Grp} H is a group isomorphism."
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
      "variable_name": "φ_hom",
      "variable_type": "G → H",
      "properties": "the underlying group homomorphism of φ.",
      "statement": "Let φ_hom : G → H denote the underlying group homomorphism of φ."
    },
    {
      "type": "assert_statement",
      "claim": "φ_hom is bijective."
    },
    {
      "type": "assert_statement",
      "claim": "φ_hom satisfies ∀ g1, g2 : G, φ_hom(g1 ·_G g2) = φ_hom(g1) ·_H φ_hom(g2)."
    },

    {
      "type": "Definition",
      "label": "def:phi_inv",
      "header": "Definition",
      "name" : "φ_inv",
      "definition": "For all h : H, φ_hom(φ_inv(h)) = h and φ_inv(φ_hom(g)) = g."
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
              "value": "φ_inv(x)",
              "statement": "Define g1 := φ_inv(x)."
            },
            {
              "type": "let_statement",
              "variable_name": "g2",
              "value": "φ_inv(y)",
              "statement": "Define g2 := φ_inv(y)."
            },
            {
              "type": "assert_statement",
              "claim": "φ_hom(g1) = x",
              "internal_references": [
                {
                  "target_identifier": "def:phi_hom"
                }
              ]
            },
            {
              "type": "assert_statement",
              "claim": "φ_hom(g2) = y",
              "internal_references": [
                {
                  "target_identifier": "def:phi_hom"
                }
              ]
            },
            {
              "type": "assert_statement",
              "claim": "x ·_H y = φ_hom(g1 ·_G g2)",
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
              "claim": "φ_hom(g1 ·_G g2) = y ·_H x",
              "calculation": {
                "calculation_sequence": [
                  "φ_hom(g1 ·_G g2) = φ_hom(g2 ·_G g1)",
                  "φ_hom(g2 ·_G g1) = φ_hom(g2) ·_H φ_hom(g1)",
                  "φ_hom(g2) ·_H φ_hom(g1) = y ·_H x"
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


/-!
Generated code for the above JSON structure.
* Definitions did not translate to Lean code even as assertions.
* The main theorem was translated to a theorem with a proof.
* The scoped notation for the Euler totient function created an error with some translations.
-/
#check "Error: codegen: no valid function found for key assert_statement"
#check "Tried functions: #[LeanAide.assertionCode]"
#check "Errors in functions:"
#check ""
#check
  "LeanAide.assertionCode: codegen: failed to translate 'φ_hom is bijective.' to a proposition even with 'full statement', error: codegen: no valid type found for assertion 'φ_hom is bijective.', full statement Let φ_hom : G → H denote the underlying group homomorphism of φ."
#check "φ_hom is bijective.; all translations:"
#check ""
#check
  "{G : Type u} {H : Type v} [instG : Group G] [instH : Group H] {φ : G →* H}, Function.Bijective φ.toFun"
#check "∀ {G H : Type u} [Group G] [Group H] (φ : G ≃* H), Function.Bijective φ.toMonoidHom"
#check "∀ {G : Type u} {H : Type v} [Group G] [Group H] (φ : G →* H), Function.Bijective φ.toFun"
#check
  "∀ {G H : Type u_1} [instG : Group G] [instH : Group H] (φ : G ≃* H), Function.Bijective φ_hom"
#check "∀ {G H : Type u} [Group G] [Group H] (φ : G ≃* H), Function.Bijective (φ : G →* H)"
#check "∀ {G H : Type u} [instG : Group G] [instH : Group H] (φ : G ≃* H),"
#check "  Function.Bijective φ.toMonoidHom"
#check
  "∀ {G : Type u} {H : Type v} [instG : Group G] [instH : Group H] (φ : G ≃* H), Function.Bijective (φ : G → H)"
#check "∀ {G H : Type u} [instG : Group G] [instH : Group H] (φ : G ≃* H),"
#check
  "  Function.Bijective (φ : G → H); full claim: The map \\( \\varphi_{\\text{hom}} \\) is bijective., error: codegen: no valid type found for assertion 'The map \\( \\varphi_{\\text{hom}} \\) is bijective.', full statement Let φ_hom : G → H denote the underlying group homomorphism of φ."
#check "The map \\( \\varphi_{\\text{hom}} \\) is bijective.; all translations:"
#check ""
#check
  "∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : Group H] {φ : G ≃* H}, Function.Bijective φ.toMonoidHom"
#check "∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : Group H] (φ : G ≃* H),"
#check "  Function.Bijective (φ : G → H)"
#check "∀ {G : Type u} {H : Type v} [instG : Group G] [instH : Group H] (φ : G ≃* H),"
#check "  Function.Bijective φ.toMonoidHom"
#check "∀ {G : Type u} {H : Type v} [inst : Group G] [inst_1 : Group H] "
#check "  (φ : G ≃* H), Function.Bijective (φ : G → H)"
#check
  "{G : Type u} {H : Type v} [instG : Group G] [instH : Group H] (φ : G →* H), Function.Bijective φ.toHom"
#check
  "∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : Group H] (φ : G →* H), Function.Bijective φ_hom"
#check
  "∀ {G : Type u_1} {H : Type u_2} [Group G] [Group H] (φ : G ≃* H), Function.Bijective φ.toMonoidHom"
#check "∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : Group H] {φ : G ≃* H},"
#check "  Function.Bijective (φ : G → H)"
#check "source:"
#check "{\"claim\": \"φ_hom is bijective.\"}"
theorem assert_2611128936540923388 : ∀ {g1 g2 : ℕ}, φ (g1 * g2) = φ g1 * φ g2 :=
  by
  trace "Automation Tactics hammer {aesopPremises := 5, autoPremises := 0} [] for goal: ∀ {g1 g2 : ℕ}, φ (g1 * g2) = φ g1 * φ g2"
  intro g1 g2
  sorry
  trace "Finished Automation Tactics hammer {aesopPremises := 5, autoPremises := 0} [] for goal: ∀ {g1 g2 : ℕ}, φ (g1 * g2) = φ g1 * φ g2"
theorem isomorphism_inv_exists :
    ∀ {G H : Type u_1} [inst : Group G] [inst_1 : Group H] (φ_hom : G →* H),
      ∃ (φ_inv : H → G),
        (∀ (h : H), (φ_hom : G → H) (φ_inv h) = h) ∧ ∀ (g : G), φ_inv ((φ_hom : G → H) g) = g :=
  by
  trace
    "Automation Tactics hammer {aesopPremises := 5, autoPremises := 0} for goal: ∀ {G H : Type u_1} [inst : Group G] [inst_1 : Group H] (φ_hom : G →* H),\n  ∃ φ_inv, (∀ (h : H), φ_hom (φ_inv h) = h) ∧ ∀ (g : G), φ_inv (φ_hom g) = g"
  intro G H inst inst_1 φ_hom
  sorry
  trace
    "Finished Automation Tactics hammer {aesopPremises := 5, autoPremises := 0} for goal: ∀ {G H : Type u_1} [inst : Group G] [inst_1 : Group H] (φ_hom : G →* H),\n  ∃ φ_inv, (∀ (h : H), φ_hom (φ_inv h) = h) ∧ ∀ (g : G), φ_inv (φ_hom g) = g"
theorem comm_group_of_abelian_codomain :
    ∀ {G : Type u} {H : Type v} [inst : Group G] [inst_1 : CommGroup H] (φ_hom : G →* H)
      (x y : H), x * y = y * x :=
  by
  intro G H inst inst_1 φ_hom x y
  exact CommGroup.mul_comm x y

/-!
Locating errors:
* The first translation partly worked except that `φ` means the null set and cannot be used as a variable and there may have been a comma.
* The error was "unexpected token '\'; expected '_' or identifier"
* Can use a retranslation to fix this (detect presence of `φ`).
-/
example  : ∀ {G : Type u} {H : Type v} [Group G] [Group H] (ϕ : G →* H), Function.Bijective ϕ.toFun := by sorry

example: ∀ {G H : Type u} [Group G] [Group H] (ϕ : G ≃* H), Function.Bijective ϕ.toMonoidHom := by sorry

#eval 'φ' = 'ϕ'

#eval Name.anonymous.toString -- "[anonymous]"

/-!
Switching to `ϕ`.
-/
