import Mathlib
import LeanAide.AutoTactic
import LeanAide.Syntax
universe u v u_1
set_option maxHeartbeats 10000000
set_option linter.unreachableTactic false

-- DEMO example

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

theorem aux_17159876999765957439 : ∀ (n : ℕ), Even (n * (n + 1)) :=
  by
  intro n
  #note["Failed to translate calculation {\"inline_calculation\":\"n(n+1)\"}"]
  by_cases Even n
  case pos =>
    have assert_5319112468382426543 : ∃ k, ↑n = 2 * k := by auto?[]
    have calculation_14047433094544108429 : ∀ (k : ℕ), n * (n + 1) = 2 * k * (n + 1) := by auto?
    have assert_4302669041932502115 : ∀ (k : ℕ), Even (2 * k * (n + 1)) := by auto?[]
    auto?
  case neg =>
    have cond_2667733541464095191 : Odd n ↔ ∃ k, n = 2 * k + 1 := by auto?
    have assert_758821247436174302 : ∃ k, ↑n = 2 * k + 1 := by auto?[]
    have calculation_11041185977590610505 : ∀ {k : ℕ}, n + 1 = 2 * k + 2 ↔ n + 1 = 2 * (k + 1) := by auto?
    have calculation_17388922601861285712 : n * (n + 1) = (2 * n + 1) * (n + 1) := by auto?
    have calculation_17817816054343669924 : ∀ (k : ℕ), n * (n + 1) = 2 * (2 * k ^ 2 + 3 * k + 1) := by auto?
    have assert_1018076716932953991 : ∀ (k : ℕ), Even (2 * (2 * k ^ 2 + 3 * k + 1)) := by auto?[]
    auto?
  first
  | done
  | have conclusion_15884785423130108433 : Even (n * (n + 1)) := by auto?
  auto?

/-!
## Elaboration logs
Try this:
(plausible_sorry)
Try this:
  intro k
  simp_all only [mul_eq_mul_right_iff, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, or_false]
  obtain ⟨w, h_1⟩ := assert_5319112468382426543
  subst h_1
  simp_all only [even_two, Even.mul_right, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]
  (plausible_sorry)
Try this:
  intro k
  simp_all only [mul_eq_mul_right_iff, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, or_false, even_two,
    Even.mul_right]
Try this:
simp_all only [mul_eq_mul_right_iff, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, or_false, even_two,
    Even.mul_right, implies_true]
Try this:
  rename_i h
  simp_all only [Nat.not_even_iff_odd, true_iff]
  exact h
Try this:
simp_all only [Nat.not_even_iff_odd, iff_true]
Try this:
  rename_i h
  intro k
  simp_all only [Nat.not_even_iff_odd, iff_true, add_left_inj]
  obtain ⟨w, h⟩ := assert_758821247436174302
  subst h
  simp_all only [even_two, Even.mul_right, Even.add_one, add_left_inj, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero,
    or_false]
  apply Iff.intro
  · intro a
    subst a
    rfl
  · intro a
    (omega)
Try this:
  rename_i h
  simp_all only [Nat.not_even_iff_odd, iff_true, add_left_inj, mul_eq_mul_right_iff, ne_eq,
    AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true, right_eq_mul₀, OfNat.ofNat_ne_one,
    or_self]
  obtain ⟨w, h⟩ := assert_758821247436174302
  simp_all only [mul_eq_mul_left_iff, add_left_inj, OfNat.ofNat_ne_zero, or_false]
  (plausible_sorry)
Try this:
  intro k
  simp_all only [Nat.not_even_iff_odd, iff_true, add_left_inj, mul_eq_mul_right_iff, ne_eq,
    AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true, right_eq_mul₀, OfNat.ofNat_ne_one,
    or_self]
Try this:
  intro k
  simp_all only [Nat.not_even_iff_odd, iff_true, add_left_inj, mul_eq_mul_right_iff, ne_eq,
    AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true, right_eq_mul₀, OfNat.ofNat_ne_one,
    or_self]
Try this:
simp_all only [Nat.not_even_iff_odd, iff_true, add_left_inj, mul_eq_mul_right_iff, ne_eq,
    AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true, right_eq_mul₀, OfNat.ofNat_ne_one,
    or_self]
declaration uses 'sorry'
this tactic is never executed
note: this linter can be disabled with `set_option linter.unreachableTactic false`
'#note["Failed to translate calculation {\"inline_calculation\":\"n(n+1)\"}"]' tactic does nothing
note: this linter can be disabled with `set_option linter.unusedTactic false`
'first
| done
| have conclusion_15884785423130108433 : Even (n * (n + 1)) := by auto?' tactic does nothing
note: this linter can be disabled with `set_option linter.unusedTactic false`
'auto?' tactic does nothing
note: this linter can be disabled with `set_option linter.unusedTactic false`

* Sorries in aux_17159876999765957439:

 * `∀ (n : ℕ), Even n → ∃ k, n = 2 * k`
 * `∀ (n : ℕ), Even n → (∃ k, n = 2 * k) → ∀ (k w : ℕ), n = 2 * w → Even (2 * w) → w = k`
 * `∀ (n : ℕ),   ¬Even n →     (Odd n ↔ ∃ k, n = 2 * k + 1) →       (∃ k, n = 2 * k + 1) →         (∀ {k : ℕ}, n + 1 = 2 * k + 2 ↔ n + 1 = 2 * (k + 1)) → ∀ (w : ℕ), n + 1 = 2 * (w + 1) → False`
-/
