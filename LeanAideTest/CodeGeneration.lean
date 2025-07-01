import LeanAide
import Lean
import Qq

open LeanAide Lean Meta Elab Parser Tactic

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
    "value": "n is odd",
    "properties": "n > 0"
  }

open Codegen
#eval showStx egTheorem

#eval showStx egTheorem''


#eval egTheorem


#eval showStx egLet

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

example: ∀ (N : ℤ), N % 10 = 0 ∨ N % 10 = 5 → 5 ∣ N := by
  intro
  aesop?
  · sorry
  · sorry

#eval (ChatServer.default).fullStatement "p ∤ m!"

#eval Translator.translateToPropStrict "p ∤ m!" {}
