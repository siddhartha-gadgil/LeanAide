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

  theorem fortyTwoPos : 42 > 0 :=
    by
    trace "Automation tactics found for 42 > 0, closing goal"
    simp_all only [gt_iff_lt, ofNat_pos]
  #check "fortyTwoPos has type 42 > 0"
  theorem fortyTwoNeg : 42 < 0 := by sorry
  example : 0 < 42 :=
    fortyTwoPos

#eval ``commandSeq

#codegen {"lean": "example : 0 < 42 := by decide"}
