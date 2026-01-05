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
    "claim" : "∀ f: ℕ → ℕ, f 0 = 0 → (∀ n: ℕ, f (n + 1) = f n + 1) → ∀ n: ℕ, f n = n",
    "proof" : {"induction_proof" : {
      "on" : "n",
      "base_case_proof" : [],
      "induction_step_proof" : []
    }
  }}
}

/--
info: codegen: trying LeanAide.theoremCode for key theorem
---
info: codegen: trying LeanAide.inductionCode for key induction_proof
---
info: codegen: trying LeanAide.documentCode for key document
---
info: codegen: trying LeanAide.documentCode for key document
---
info: All theorems : [forall_nat_cast_succ_eq_add_one_then_eq_id]
---
info: Try this: theorem forall_nat_cast_succ_eq_add_one_then_eq_id :
      ∀ (f : ℕ → ℕ), f 0 = 0 → (∀ (n : ℕ), f (n + 1) = f n + 1) → ∀ (n : ℕ), f n = n :=
    by
    intro f a_1676541840746925941 a_2213797161315613598 n
    induction n with
    | zero =>
      trace "Automation tactics found for f 0 = 0, closing goal"
      grind only
    | succ n ih =>
      trace "Automation tactics found for f (n + 1) = n + 1, closing goal"
      grind only
    done
-/
#guard_msgs in
#codegen induction_eg

theorem forall_nat_cast_succ_eq_add_one_then_eq_id :
      ∀ (f : ℕ → ℕ), f 0 = 0 → (∀ (n : ℕ), f (n + 1) = f n + 1) → ∀ (n : ℕ), f n = n :=
    by
    intro f a_1676541840746925941 a_2213797161315613598 n
    induction n with
    | zero =>
      trace "Automation tactics found for f 0 = 0, closing goal"
      grind only
    | succ n ih =>
      trace "Automation tactics found for f (n + 1) = n + 1, closing goal"
      grind only
    done

def pattern_eg := json% {
  "theorem" : {
    "claim" : "∀ n : ℕ, (fun x => 1 + x)^[n] 0 = n",
    "proof" : {"pattern_cases_proof" : {
      "on" : "n",
      "proof_cases" : [
        {"pattern" : "0", "proof" : []},
        {"pattern" : "n + 1", "proof" : []}
      ]
    }
  }}
}

/--
info: codegen: trying LeanAide.theoremCode for key theorem
---
info: codegen: trying LeanAide.patternCasesCode for key pattern_cases_proof
---
info: codegen: trying LeanAide.documentCode for key document
---
info: codegen: trying LeanAide.documentCode for key document
---
info: All theorems : [iterate_add_one_apply_eq_self]
---
info: Try this: theorem iterate_add_one_apply_eq_self : ∀ (n : ℕ), (fun (x : ℕ) ↦ 1 + x)^[n] 0 = n :=
    by
    intro n
    match c_12041890053830139676 : n with
    | 0 =>
      trace "Automation tactics found for (fun x => 1 + x)^[0] 0 = 0, closing goal"
      simp only [Function.iterate_zero, id_eq]
    | n + 1 =>
      trace "Automation tactics found for (fun x => 1 + x)^[n + 1] 0 = n + 1, closing goal"
      simp only [Function.iterate_succ, add_left_iterate, Lake.FamilyOut.fam_eq, smul_eq_mul, mul_one,
        Function.comp_apply, add_zero, Nat.add_left_cancel_iff]
-/
#guard_msgs in
#codegen pattern_eg

example : ∀ n : ℕ, n = 1  ∨ n = 2 → n < 3 := by
  intro n h
  if c: n = 1 then
    aesop
  else if c': n = 2 then
    aesop
  else
    aesop

def multiConditionEg := json% {
  "theorem" : {
    "claim" : "∀ n : ℕ, n = 1  ∨ n = 2 → n < 3",
    "proof" : {"multi-condition_cases_proof" : {
      "on" : "n",
      "proof_cases" : [
        {"condition" : "n = 1", "proof" : []},
        {"condition" : "n = 2", "proof" : []}
      ]
    }
  }}
}

/--
info: codegen: trying LeanAide.theoremCode for key theorem
---
info: codegen: trying LeanAide.multiConditionCasesCode for key multi-condition_cases_proof
---
info: codegen: trying LeanAide.documentCode for key document
---
info: codegen: trying LeanAide.documentCode for key document
---
info: All theorems : [nat_eq_one_or_eq_two_imp_lt_three]
---
info: Try this: theorem nat_eq_one_or_eq_two_imp_lt_three : ∀ (n : ℕ), n = 1 ∨ n = 2 → n < 3 :=
    by
    intro n a_12668439849020315063
    if condition_15952715909003343985 : n = 1 then
      ⏎
      trace "Automation tactics found for n < 3, closing goal"
      grind only
    else
      if condition_1530173634913780371 : n = 2 then
        ⏎
        trace "Automation tactics found for n < 3, closing goal"
        grind only
      else
        trace
          "Automation Tactics   simp?\n  try simp?; exact?\n  grind?\n  hammer {aesopPremises := 5, autoPremises := 0} for goal: n < 3"
        grind only
        trace
          "Finished Automation Tactics   simp?\n  try simp?; exact?\n  grind?\n  hammer {aesopPremises := 5, autoPremises := 0} for goal: n < 3"
    done
-/
#guard_msgs in
#codegen multiConditionEg

-- Output:
theorem nat_eq_one_or_eq_two_imp_lt_three : ∀ (n : ℕ), n = 1 ∨ n = 2 → n < 3 :=
    by
    intro n a_12668439849020315063
    if condition_15952715909003343985 : n = 1 then

      trace "Automation tactics found for n < 3, closing goal"
      subst condition_15952715909003343985
      simp_all only [OfNat.one_ne_ofNat, or_false, one_lt_ofNat]
    else
      if condition_1530173634913780371 : n = 2 then

        trace "Automation tactics found for n < 3, closing goal"
        subst condition_1530173634913780371
        simp_all only [or_true, OfNat.ofNat_ne_one, not_false_eq_true, Nat.lt_add_one]
      else
        trace
          "Automation Tactics first\n  | (simp?; done)\n  | hammer {aesopPremises := 5, autoPremises := 0} for goal: n < 3"
        simp_all only [or_self]
        trace
          "Finished Automation Tactics first\n  | (simp?; done)\n  | hammer {aesopPremises := 5, autoPremises := 0} for goal: n < 3"
    done


def patternEg' := json% {
  "theorem" : {
    "claim" : "∀ n : ℕ, n = 1  ∨ n = 4 → n < 5",
    "proof" : {"pattern_cases_proof" : {
      "on" : "n",
      "proof_cases" : [
        {"pattern" : "1", "proof" : []},
        {"pattern" : "4", "proof" : []}
      ]
    }
  }}
}

/--
info: codegen: trying LeanAide.theoremCode for key theorem
---
info: codegen: trying LeanAide.patternCasesCode for key pattern_cases_proof
---
info: codegen: trying LeanAide.documentCode for key document
---
info: codegen: trying LeanAide.documentCode for key document
---
info: All theorems : [nat.eq_one_or_eq_four_imp_lt_five]
---
info: Try this: theorem nat.eq_one_or_eq_four_imp_lt_five : ∀ (n : ℕ), n = 1 ∨ n = 4 → n < 5 :=
    by
    intro n a_16768665977230715297
    match c_12041890053830139676 : n with
    | 1 =>
      trace "Automation tactics found for 1 < 5, closing goal"
      simp only [Nat.one_lt_ofNat]
    | 4 =>
      trace "Automation tactics found for 4 < 5, closing goal"
      simp only [Nat.lt_add_one]
-/
#guard_msgs in
#codegen patternEg'

-- Output:

theorem nat.eq_one_or_eq_four_imp_lt_five : ∀ (n : ℕ), n = 1 ∨ n = 4 → n < 5 :=
    by
    intro n a_16768665977230715297
    match c_12041890053830139676 : n with
    | 1 =>
      trace "Automation tactics found for 1 < 5, closing goal"
      simp only [one_lt_ofNat]
    | 4 =>
      trace "Automation tactics found for 4 < 5, closing goal"
      simp only [Nat.lt_add_one]

/-- info: Int.ofNat 3 -/
#guard_msgs in
#eval 1 + 2
