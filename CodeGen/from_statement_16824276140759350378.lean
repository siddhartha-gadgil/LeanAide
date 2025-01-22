import Mathlib
import LeanAide.AutoTactic
import LeanAide.Syntax
universe u v u_1
set_option maxHeartbeats 10000000
set_option linter.unreachableTactic false


/-!
## Theorem
The product of two successive natural numbers is even.
## Proof
Let \( n \) be a natural number. The two successive natural numbers are \( n \) and \( n+1 \). We consider the product \( n(n+1) \).

There are two cases to consider:
1. If \( n \) is even, then \( n = 2k \) for some integer \( k \). Hence,
   \[
   n(n+1) = 2k(n+1),
   \]
   which is clearly even because it is divisible by 2.

2. If \( n \) is odd, then \( n = 2k + 1 \) for some integer \( k \). Hence,
   \[
   n+1 = 2k+2 = 2(k+1).
   \]
   Thus,
   \[
   n(n+1) = (2k+1) \cdot 2(k+1) = 2 \times (2k^2 + 3k + 1),
   \]
   which is also even because it is divisible by 2.

In either case, the product \( n(n+1) \) is even. Therefore, the product of any two successive natural numbers is even.

## JSON structured proof
{"math_document":
 [{"theorem":
   {"proved": true,
    "proof":
    [{"let":
      {"variable": "<anonymous>",
       "value": "n and n+1",
       "kind": "successive natural numbers"}},
     {"calculate": {"inline_calculation": "n(n+1)"}},
     {"cases":
      {"split_kind": "condition",
       "proof_cases":
       [{"case":
         {"proof":
          [{"assert":
            {"proof_method": "definition of even number",
             "claim": "n = 2k for some integer k"}},
           {"calculate":
            {"calculation_sequence":
             [{"calculation_step": "n(n+1) = 2k(n+1)"}]}},
           {"assert":
            {"proof_method": "since it is divisible by 2",
             "claim": "2k(n+1) is even"}}],
          "condition": "n is even"}},
        {"case":
         {"proof":
          [{"assert":
            {"proof_method": "definition of odd number",
             "claim": "n = 2k + 1 for some integer k"}},
           {"calculate":
            {"calculation_sequence":
             [{"calculation_step": "n+1 = 2k + 2 = 2(k + 1)"},
              {"calculation_step": "n(n+1) = (2k + 1) · 2(k + 1)"},
              {"calculation_step": "n(n+1) = 2(2k^2 + 3k + 1)"}]}},
           {"assert":
            {"proof_method": "since it is divisible by 2",
             "claim": "2(2k^2 + 3k + 1) is even"}}],
          "condition": "n is odd"}}],
       "on": "n",
       "exhaustiveness":
       [{"assert":
         {"proof_method": "by definition of the parity of integers",
          "claim": "n is either even or odd"}}]}},
     {"conclude":
      {"claim": "The product of any two successive natural numbers is even."}}],
    "hypothesis": [{"let": {"variable": "n", "kind": "natural number"}}],
    "conclusion": "The product of two successive natural numbers is even."}}]}-/

theorem nat.even_mul_succ_self : ∀ (n : ℕ), Even (n * (n + 1)) :=
  by
  intro n
  #note["Failed to translate calculation {\"inline_calculation\":\"n(n+1)\"}"]
  if Even n then 
    have assert_6170125354565453887 : ∃ (k : ℤ), (↑n : ℤ) = 2 * k := by auto? []
    have ⟨k, assert_5821292936828346117⟩ := assert_6170125354565453887
    have calculation_14047433094544108429 : (↑n : ℤ) * ((↑n : ℤ) + 1) = 2 * k * ((↑n : ℤ) + 1) := by auto?
    have assert_15964048830528568915 : Even (2 * k * ((↑n : ℤ) + 1)) := by auto? []
    auto?
  else
    have cond_2667733541464095191 : Odd n := by auto?
    have assert_17553354813198403715 : ∃ (k : ℤ), (↑n : ℤ) = 2 * k + 1 := by auto? []
    have ⟨k, assert_14953524905262294969⟩ := assert_17553354813198403715
    have calculation_11041185977590610505 : (↑n : ℤ) + 1 = 2 * k + 2 → (↑n : ℤ) + 1 = 2 * (k + 1) := by auto?
    have calculation_17388922601861285712 : (↑n : ℤ) * ((↑n : ℤ) + 1) = (2 * k + 1) * 2 * (k + 1) := by auto?
    have calculation_17817816054343669924 : (↑n : ℤ) * ((↑n : ℤ) + 1) = 2 * (2 * k ^ 2 + 3 * k + 1) := by auto?
    have assert_17437420099303118664 : Even (2 * (2 * k ^ 2 + 3 * k + 1)) := by auto? []
    auto?

/-!
## Elaboration logs
tactic 'aesop' failed, made no progress
Initial goal:
  n : ℕ
  h✝ : Even n
  ⊢ ∃ k, ↑n = 2 * k
Try this:
(plausible_sorry)
Try this:
simp_all only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, exists_eq']
Try this:
simp_all only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, exists_eq', even_two, Even.mul_right]
Try this:
simp_all only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, exists_eq', even_two, Even.mul_right]
Try this:
simp_all only [Nat.not_even_iff_odd]
Try this:
  simp_all only [Nat.not_even_iff_odd]
  sorry
aesop: maximum number of rule applications (200) reached. Set the 'maxRuleApplications' option to increase the limit.
Try this:
(plausible_sorry)
Try this:
  intro a
  simp_all only [Nat.not_even_iff_odd, add_left_inj, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, exists_eq']
  (ring)
Try this:
  simp_all only [Nat.not_even_iff_odd, add_left_inj, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, exists_eq']
  (ring)
Try this:
  simp_all only [Nat.not_even_iff_odd, add_left_inj, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, exists_eq']
  (ring)
Try this:
simp_all only [Nat.not_even_iff_odd, add_left_inj, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, exists_eq',
    even_two, Even.mul_right]
Try this:
simp_all only [Nat.not_even_iff_odd, add_left_inj, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, exists_eq',
    even_two, Even.mul_right, Odd.add_one, Even.mul_left]
declaration uses 'sorry'
'#note["Failed to translate calculation {\"inline_calculation\":\"n(n+1)\"}"]' tactic does nothing
note: this linter can be disabled with `set_option linter.unusedTactic false`

* Sorries in nat.even_mul_succ_self:

 * `∀ (n : ℕ), Even n → ∃ k, ↑n = 2 * k`
 * `∀ (n : ℕ), ¬Even n → Odd n → ∃ k, ↑n = 2 * k + 1`
-/
