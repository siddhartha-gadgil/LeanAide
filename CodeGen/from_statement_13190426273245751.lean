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

theorem aux_17159876999765957439 : ∀ (n : ℕ), Even (n * (n + 1)) :=
  by
  intro n
  have calculation_12928321614448728289 : n * (n + 1) = Nat.succ n * n := by auto?
  if Even n → Even (n + 1) then

    have assert_6170125354565453887 : ∃ (k : ℤ), (↑n : ℤ) = 2 * k := by auto? []
    have ⟨k, assert_5821292936828346117⟩ := assert_6170125354565453887
    have calculation_14047433094544108429 : ∀ (k : ℕ), n * (n + 1) = 2 * k * (n + 1) := by auto?
    have assert_8019456335182814933 : ∀ {k : ℕ}, Even (2 * k * (n + 1)) := by auto? []
    auto?
  else
    have cond_2667733541464095191 : Odd n := by auto?
    have assert_17553354813198403715 : ∃ (k : ℤ), (↑n : ℤ) = 2 * k + 1 := by auto? []
    have ⟨k, assert_14953524905262294969⟩ := assert_17553354813198403715
    have calculation_11041185977590610505 : ∀ (k : ℕ), n + 1 = 2 * k + 2 → n + 1 = 2 * (k + 1) := by auto?
    have calculation_17388922601861285712 : ∃ (k : ℕ), n * (n + 1) = (2 * k + 1) * 2 * (k + 1) := by auto?
    have calculation_17817816054343669924 : ∃ (k : ℕ), n * (n + 1) = 2 * (2 * k ^ 2 + 3 * k + 1) := by auto?
    have assert_1018076716932953991 : ∀ (k : ℕ), Even (2 * (2 * k ^ 2 + 3 * k + 1)) := by auto? []
    auto?

/-!
## Elaboration logs
Try this:
  simp_all only [Nat.succ_eq_add_one]
  (ring)
Try this:
  simp_all only [Nat.succ_eq_add_one]
  sorry
aesop: maximum number of rule applications (200) reached. Set the 'maxRuleApplications' option to increase the limit.
Try this:
(plausible_sorry)
(deterministic) timeout at `aesop`, maximum number of heartbeats (200000) has been reached
Use `set_option maxHeartbeats <num>` to set the limit.
Additional diagnostic information may be available using the `set_option diagnostics true` command.
(deterministic) timeout at `aesop`, maximum number of heartbeats (200000) has been reached
Use `set_option maxHeartbeats <num>` to set the limit.
Additional diagnostic information may be available using the `set_option diagnostics true` command.
(deterministic) timeout at `elaborator`, maximum number of heartbeats (200000) has been reached
Use `set_option maxHeartbeats <num>` to set the limit.
Additional diagnostic information may be available using the `set_option diagnostics true` command.
(deterministic) timeout at `elaborator`, maximum number of heartbeats (200000) has been reached
Use `set_option maxHeartbeats <num>` to set the limit.
Additional diagnostic information may be available using the `set_option diagnostics true` command.
(deterministic) timeout at `elaborator`, maximum number of heartbeats (200000) has been reached
Use `set_option maxHeartbeats <num>` to set the limit.
Additional diagnostic information may be available using the `set_option diagnostics true` command.

* Sorries in aux_17159876999765957439:

 * `∀ (n : ℕ), n * (n + 1) = n.succ * n → (Even n → Even (n + 1)) → Even (n * (n + 1))`
 * `∀ (n : ℕ), n * (n + 1) = n.succ * n → ¬(Even n → Even (n + 1)) → Even (n * (n + 1))`
-/
