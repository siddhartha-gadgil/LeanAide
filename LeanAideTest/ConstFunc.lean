import Mathlib
import LeanAide
open Nat LeanAide
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe u v u_1

namespace LeanAide.ConstFunc
def constFuncStructured := json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "header": "Theorem",
        "label": "thm:constant_sequence",
        "hypothesis": [
          {
            "type": "let_statement",
            "variable_name": "(a_n)",
            "statement": "Let $(a_n)$ be a sequence
			defined by $a_0=c$ and $a_{n+1} = a_n$ for all $n$."
          }
        ],
        "claim": "$a_n = c$ for all $n$.",
        "proof": [
          {
            "type": "induction_proof",
            "on": "n",
            "base_case_proof": [
              {
                "type": "assert_statement",
                "claim": "$a_0 = c$",
                "proof_method": "by definition"
              }
            ],
            "induction_step_proof": [
              {
                "type": "assume_statement",
                "assumption": "Assume $a_n = c$."
              },
              {
                "type": "calculation",
                "inline_calculation": "a_{n+1} = a_n = c",
                "calculation_sequence": [
                  "a_{n+1} = a_n",
                  "= c"
                ]
              }
            ]
          },
          {
            "type": "conclude_statement",
            "claim": "Thus $a_n = c$ for all $n$."
          }
        ]
      }
    ]
  }
}

/--
warning: Found 3038 unindexed premises in the environment, which exceeds the maximum number of new premises (2048). Discarding premises beyond this limit
---
warning: Found 3038 unindexed premises in the environment, which exceeds the maximum number of new premises (2048). Discarding premises beyond this limit
---
warning: Found 3038 unindexed premises in the environment, which exceeds the maximum number of new premises (2048). Discarding premises beyond this limit
---
warning: Found 3038 unindexed premises in the environment, which exceeds the maximum number of new premises (2048). Discarding premises beyond this limit
---
warning: Found 3038 unindexed premises in the environment, which exceeds the maximum number of new premises (2048). Discarding premises beyond this limit
---
warning: Found 3038 unindexed premises in the environment, which exceeds the maximum number of new premises (2048). Discarding premises beyond this limit
---
info: All theorems : [thm:constant_sequence]
---
info: Try this:
  [apply] theorem eq_const_of_succ_eq_self :
        ∀ {α : Type u_1} (a : ℕ → α) (c : α), a (0 : ℕ) = c → (∀ (n : ℕ), a (n + (1 : ℕ)) = a n) → ∀ (n : ℕ), a n = c :=
      by
      intro α a c a_18193650970466190054 a_18068984259474765511 n
      induction n with
      | zero => grind only
      | succ n ih => grind only [#4b08]
      done
-/
#guard_msgs in
#codegen constFuncStructured


end LeanAide.ConstFunc
