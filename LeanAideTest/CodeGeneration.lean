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
  hammer

theorem nat_lt_succ : ∀ (n : ℕ), n < succ n := by
    intro n
    trace "Automation tactics found for n < n.succ, closing goal"
    simp_all only [succ_eq_add_one, lt_add_iff_pos_right, lt_one_iff, pos_of_gt]
