import LeanAide

open LeanAide Lean Meta Elab Parser Tactic
set_option linter.unusedTactic false

open Nat

namespace LeanAideTest.SmallCodes

def eg₁ : Json := json% {
  "document" : [
    {
      "theorem" : {
        "name" : "fortyTwoPos",
        "claim" : "42 > 0",
        "proof" : {
          "proof_steps" : [{"lean": "decide"}]
        }
        }
      },
      {"check" : "fortyTwoPos"},
      {
      "theorem" : {
        "name" : "fortyTwoNeg",
        "claim" : "42 < 0",
        "proof" : {
          "proof_steps" : [{"lean": "sorry"}]
        }
        }
      },
      {"lean": "example : 0 < 42 := fortyTwoPos"}
      ]
    }

-- #codegen eg₁

#eval ``commandSeq

#codegen {"lean": "example : 0 < 42 := by decide"}
