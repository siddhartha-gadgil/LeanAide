import LeanAide
import LeanAideCore.Syntax
import LeanAide.Responses
import Lean
import Qq

open LeanAide Lean Meta Elab Parser Tactic
set_option linter.unusedTactic false

open Nat

open Qq

def groupSquareIsAbelian : Json :=
  json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "label": "thm:group-square-is-abelian",
        "header": "Theorem",
        "claim": "A group G that satisfies the equality (a*b)^2 = a^2*b^2 for all a, b in G is an Abelian group.",
        "proof": [
          {
            "type": "let_statement",
            "variable_name": "G",
            "variable_type": "group",
            "statement": "Let G be a group such that for all a,b lying in G we have the equality (a*b)^2 = a^2*b^2."
          },
          {
            "type": "assert_statement",
            "claim": "For all a,b in G we have that abab = aabb.",
            "proof_method": "using the definition of the group operation and associativity to expand (a b)^2 = a^2*b^2 ."
          },
          {
            "type": "assume_statement",
            "assumption": "Fix arbitrary elements a,b in G."
          },
          {
            "type": "assert_statement",
            "claim": "abab = aabb.",
            "proof_method": "Instance of the identity abab = aabb for the fixed elements a,b."
          },
          {
            "type": "assert_statement",
            "claim": "a^{-1}(abab) = a^{-1}(aabb).",
            "proof_method": "Multiplying both sides of abab = aabb on the left by a^{-1} and using the group axioms."
          },
          {
            "type": "assert_statement",
            "claim": "(a^{-1}a)bab = (a^{-1}a)abb.",
            "proof_method": "Using the associativity of the group operation to rewrite a^{-1}(abab) and a^{-1}(aabb)."
          },
          {
            "type": "assert_statement",
            "claim": "bab = abb.",
            "proof_method": "Using a^{-1}a = e and ex = x for all x in G."
          },
          {
            "type": "assert_statement",
            "claim": "(bab)b^{-1} = (abb)b^{-1}.",
            "proof_method": "Multiplying on both sides of bab = abb on the right by b^{-1} and using the group axioms."
          },
          {
            "type": "assert_statement",
            "claim": "ba(bb^{-1}) = ab(bb^{-1}).",
            "proof_method": "Using the associativity of the group operation to rewrite (bab)b^{-1} and (abb)b^{-1}."
          },
          {
            "type": "assert_statement",
            "claim": "ba = ab.",
            "proof_method": "Using bb^{-1} = e and xe = x for all x in G."
          },
          {
            "type": "conclude_statement"
          }
        ]
      }
    ]
  }
}

#logIO leanaide.papercodes.debug
#logIO leanaide.interpreter.debug

#codegen groupSquareIsAbelian
