import LeanAide

open LeanAide Lean -- Meta Elab Parser Tactic
set_option linter.unusedTactic false

open Nat

namespace LeanAideTest.SmallCodes

def eg₁ : Json := json% {
  "document" : [
    {
      "theorem" : {
        "name" : "fortyTwoPos",
        "claim" : "42 > 0",
        "proof" : [
          {"lean": "decide"}
        ]
      }
    },
    {"check" : "fortyTwoPos"},
    {
    "theorem" : {
        "name" : "fortyTwoNeg",
        "claim" : "42 < 0",
        "proof" : [{"lean": "sorry"}]

        }
      },
      {"lean": "example : 0 < 42 := fortyTwoPos"}
      ]
    }

#codegen eg₁

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

def egNested : Json := json% {
  "document" : [
    {
      "theorem" : {
        "name" : "all_two",
        "claim" : "∀ n: Nat, n = 2",
        "proof" : [
          {"theorem" : {
        "name" : "all_one_lemma",
        "claim" : "∀ n: Nat, n = 1",
        "proof" : [{"lean": "sorry"}]}},
        {"theorem" : {
        "name" : "all_one_lemma_again",
        "claim" : "∀ n: Nat, n = 1",
        "proof" : []}},
        {"theorem" : {
        "name" : "all_two_lemma",
        "claim" : "∀ n: Nat, n = 2",
        "proof" : [{"lean": "sorry"}]}},
        {"theorem" : {
        "name" : "all_two_lemma_again",
        "claim" : "∀ n: Nat, n = 2",
        "proof" : []}}]
      }
    }
  ]}


#logIO leanaide.papercodes.debug

/--
info: All theorems : [all_one_lemma]
---
info: All theorems : [all_one_lemma, all_one_lemma_again]
---
info: All theorems : [all_one_lemma, all_one_lemma_again, all_two_lemma]
---
info: All theorems : [all_one_lemma, all_one_lemma_again, all_two_lemma, all_two]
---
info: Try this:
  [apply] theorem all_two : ∀ (n : ℕ), n = 2 := by
      intro n
      have all_one_lemma : n = 1 := by sorry
      have all_one_lemma_again : n = 1 := by assumption
      have all_two_lemma : n = 2 := by sorry
      assumption
-/
#guard_msgs in
#codegen egNested

axiom nat_eq_one : ∀ (n : ℕ), n = 1

def egNested₁ : Json := json% {
  "document" : [
    {
      "theorem" : {
        "name" : "all_one",
        "claim" : "∀ n: Nat, n + 2 = 3",
        "proof" : [
          {"theorem" : {
        "name" : "all_one_lemma",
        "claim" : "∀ n: Nat, n = 1",
        "proof" : [{"lean": "simp [nat_eq_one]"}]}},
        {"theorem" : {
        "name" : "all_one_lemma_succ",
        "claim" : "∀ n: Nat, n + 1 = 2",
        "proof" : []}}]
      }
    }
  ]}

/--
info: All theorems : [all_one_lemma]
---
info: All theorems : [all_one_lemma, all_one]
---
info: Try this:
  [apply] theorem all_one : ∀ (n : ℕ), n + 2 = 3 := by
      intro n
      have all_one_lemma : n = 1 := by simp [nat_eq_one]
      simp only [Nat.reduceEqDiff]
      exact all_one_lemma
-/
#guard_msgs in
#codegen egNested₁

def egNested₂ : Json := json% {
  "document" : [
    {
      "theorem" : {
        "name" : "all_one",
        "claim" : "∀ n: Nat, n + 2 = 4",
        "proof" : [
          {"theorem" : {
        "name" : "all_one_lemma",
        "claim" : "∀ n: Nat, n = 1",
        "proof" : [{"lean": "simp [nat_eq_one]"}]}},
        {"theorem" : {
        "name" : "all_one_lemma_succ",
        "claim" : "∀ n: Nat, n + 1 = 2",
        "proof" : []}}]
      }
    }
  ]}

theorem all_one : ∀ (n : ℕ), n + 2 = 4 := by
    intro n
    have all_one_lemma : n = 1 := by simp [nat_eq_one]
    have all_one_lemma_succ : n + 1 = 2 :=
      by
      simp only [Nat.reduceEqDiff]
      exact all_one_lemma
    repeat (sorry)

example : (n : ℕ) →
  let all_one_lemma : n = 1 := of_eq_true (Eq.trans (congrArg (fun (x : ℕ) ↦ x = 1) (nat_eq_one n)) (eq_self 1));
  n + 2 = 3 := by
  intro n all_one_lemma
  simp; exact?

#logIO leanaide.interpreter.debug

#codegen egNested₁
