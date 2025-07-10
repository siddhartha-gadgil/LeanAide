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
    simp only [gt_iff_lt, ofNat_pos]
  #check "fortyTwoPos has type 42 > 0"
  theorem fortyTwoNeg : False := by sorry
  example : 0 < 42 :=
    fortyTwoPos
namespace output
  theorem fortyTwoPos : 42 > 0 :=
    by
    trace "Automation tactics found for 42 > 0, closing goal"
    simp_all only [gt_iff_lt, ofNat_pos]
  #check "fortyTwoPos has type 42 > 0"
  theorem fortyTwoNeg : 42 < 0 := by sorry
  example : 0 < 42 :=
    fortyTwoPos
end output

end LeanAideTest.SmallCodes

#eval ``commandSeq

#codegen {"lean": "example : 0 < 42 := by decide"}

def eg₂ : Json := json% {
  "document" : [
    {
      "lean" : "theorem fortyTwoPos : 42 > 0 := by decide"
    },
    {"check" : "fortyTwoPos"}
  ]
}

#codegen eg₂

def egDeferred : Json := json% {
  "document" : [
    {
      "theorem" : {
        "name" : "hard",
        "claim" : "False",
        "label" : "thm:hard"
      }
    },
    {"check" : "hard.prop"},
    {"proof": {
      "claim_label": "thm:hard",
      "proof_steps": ["sorry"]
    }},
    {"lean": "theorem hardCopy : hard.prop := hard"},
    {"check" : "hardCopy"}
  ]
}

#codegen egDeferred
