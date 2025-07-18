import Mathlib
import LeanAide
open Nat LeanAide
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/--
The schema for a proof by induction, with a base case and an induction step. For documentation only.
-/
def induction_proof_schema := json%     {"induction_proof": {
      "type": "object",
      "description": "A proof by induction, with a base case and an induction step. For strong induction or structural induction, USE INSTEAD 'general_induction_proof'.",
      "properties": {
        "type": {
          "type": "string",
          "const": "induction_proof",
          "description": "The type of this logical step."
        },
        "on": {
          "type": "string",
          "description": "The variable or expression on which induction is being done."
        },
        "prev_var": {
          "type": "string",
          "description": "(OPTIONAL) The variable `m` so that the induction case if `m + 1`. If omitted it is assumed that it is the same as the 'on' variable, i.e., the induction step is `n + 1` where `n` is the variable on which induction is done."
        },
        "base_case_proof": {
          "$ref": "#/$defs/ProofDetails",
          "description": "Proof of the base case."
        },
        "induction_step_proof": {
          "$ref": "#/$defs/ProofDetails",
          "description": "Proof of the induction step, which typically shows that if the statement holds for `n`, it holds for `n+1`."
        }
      },
      "required": [
        "type",
        "on",
        "base_case_proof",
        "induction_step_proof"
      ],
      "additionalProperties": false
    }}

def induction_eg := json% {
  "theorem" : {
    "claim" : "∀ n : ℕ, (fun x => 1 + x)^[n] 0 = n",
    "proof" : {"induction_proof" : {
      "on" : "n",
      "base_case_proof" : [],
      "induction_step_proof" : []
    }
  }}
}

#codegen induction_eg
