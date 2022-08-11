/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Order.Field
import Mathbin.RingTheory.Polynomial.Bernstein
import Mathbin.Topology.ContinuousFunction.Polynomial

/-!
# Bernstein approximations and Weierstrass' theorem

We prove that the Bernstein approximations
```
∑ k : fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k)
```
for a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` tends to infinity.

Our proof follows [Richard Beals' *Analysis, an introduction*][beals-analysis], §7D.
The original proof, due to [Bernstein](bernstein1912) in 1912, is probabilistic,
and relies on Bernoulli's theorem,
which gives bounds for how quickly the observed frequencies in a
Bernoulli trial approach the underlying probability.

The proof here does not directly rely on Bernoulli's theorem,
but can also be given a probabilistic account.
* Consider a weighted coin which with probability `x` produces heads,
  and with probability `1-x` produces tails.
* The value of `bernstein n k x` is the probability that
  such a coin gives exactly `k` heads in a sequence of `n` tosses.
* If such an appearance of `k` heads results in a payoff of `f(k / n)`,
  the `n`-th Bernstein approximation for `f` evaluated at `x` is the expected payoff.
* The main estimate in the proof bounds the probability that
  the observed frequency of heads differs from `x` by more than some `δ`,
  obtaining a bound of `(4 * n * δ^2)⁻¹`, irrespective of `x`.
* This ensures that for `n` large, the Bernstein approximation is (uniformly) close to the
  payoff function `f`.

(You don't need to think in these terms to follow the proof below: it's a giant `calc` block!)

This result proves Weierstrass' theorem that polynomials are dense in `C([0,1], ℝ)`,
although we defer an abstract statement of this until later.
-/


noncomputable section

open Classical

open BigOperators

open BoundedContinuousFunction

open UnitInterval

/-- The Bernstein polynomials, as continuous functions on `[0,1]`.
-/
def bernstein (n ν : ℕ) : C(I, ℝ) :=
  (bernsteinPolynomial ℝ n ν).toContinuousMapOn I

@[simp]
theorem bernstein_apply (n ν : ℕ) (x : I) : bernstein n ν x = n.choose ν * x ^ ν * (1 - x) ^ (n - ν) := by
  dsimp' [← bernstein, ← Polynomial.toContinuousMapOn, ← Polynomial.toContinuousMap, ← bernsteinPolynomial]
  simp

theorem bernstein_nonneg {n ν : ℕ} {x : I} : 0 ≤ bernstein n ν x := by
  simp only [← bernstein_apply]
  exact
    mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg
          (by
            unit_interval)
          _))
      (pow_nonneg
        (by
          unit_interval)
        _)

/-!
We now give a slight reformulation of `bernstein_polynomial.variance`.
-/


namespace bernstein

/-- Send `k : fin (n+1)` to the equally spaced points `k/n` in the unit interval.
-/
def z {n : ℕ} (k : Finₓ (n + 1)) : I :=
  ⟨(k : ℝ) / n, by
    cases n
    · norm_num
      
    · have h₁ : 0 < (n.succ : ℝ) := by
        exact_mod_cast Nat.succ_posₓ _
      have h₂ : ↑k ≤ n.succ := by
        exact_mod_cast Finₓ.le_last k
      rw [Set.mem_Icc, le_div_iff h₁, div_le_iff h₁]
      norm_cast
      simp [← h₂]
      ⟩

-- mathport name: «expr /ₙ»
local postfix:90 "/ₙ" => z

theorem probability (n : ℕ) (x : I) : (∑ k : Finₓ (n + 1), bernstein n k x) = 1 := by
  have := bernsteinPolynomial.sum ℝ n
  apply_fun fun p => Polynomial.aeval (x : ℝ) p  at this
  simp [← AlgHom.map_sum, ← Finset.sum_range] at this
  exact this

theorem variance {n : ℕ} (h : 0 < (n : ℝ)) (x : I) :
    (∑ k : Finₓ (n + 1), (x - k/ₙ : ℝ) ^ 2 * bernstein n k x) = x * (1 - x) / n := by
  have h' : (n : ℝ) ≠ 0 := ne_of_gtₓ h
  apply_fun fun x : ℝ => x * n using GroupWithZeroₓ.mul_right_injective h'
  apply_fun fun x : ℝ => x * n using GroupWithZeroₓ.mul_right_injective h'
  dsimp'
  conv_lhs => simp only [← Finset.sum_mul, ← z]
  conv_rhs => rw [div_mul_cancel _ h']
  have := bernsteinPolynomial.variance ℝ n
  apply_fun fun p => Polynomial.aeval (x : ℝ) p  at this
  simp [← AlgHom.map_sum, ← Finset.sum_range, Polynomial.nat_cast_mul] at this
  convert this using 1
  · congr 1
    funext k
    rw [mul_comm _ (n : ℝ), mul_comm _ (n : ℝ), ← mul_assoc, ← mul_assoc]
    congr 1
    field_simp [← h]
    ring
    
  · ring
    

end bernstein

open bernstein

-- mathport name: «expr /ₙ»
local postfix:1024 "/ₙ" => z

/-- The `n`-th approximation of a continuous function on `[0,1]` by Bernstein polynomials,
given by `∑ k, f (k/n) * bernstein n k x`.
-/
def bernsteinApproximation (n : ℕ) (f : C(I, ℝ)) : C(I, ℝ) :=
  ∑ k : Finₓ (n + 1), f k/ₙ • bernstein n k

/-!
We now set up some of the basic machinery of the proof that the Bernstein approximations
converge uniformly.

A key player is the set `S f ε h n x`,
for some function `f : C(I, ℝ)`, `h : 0 < ε`, `n : ℕ` and `x : I`.

This is the set of points `k` in `fin (n+1)` such that
`k/n` is within `δ` of `x`, where `δ` is the modulus of uniform continuity for `f`,
chosen so `|f x - f y| < ε/2` when `|x - y| < δ`.

We show that if `k ∉ S`, then `1 ≤ δ^-2 * (x - k/n)^2`.
-/


namespace bernsteinApproximation

@[simp]
theorem apply (n : ℕ) (f : C(I, ℝ)) (x : I) :
    bernsteinApproximation n f x = ∑ k : Finₓ (n + 1), f k/ₙ * bernstein n k x := by
  simp [← bernsteinApproximation]

/-- The modulus of (uniform) continuity for `f`, chosen so `|f x - f y| < ε/2` when `|x - y| < δ`.
-/
def δ (f : C(I, ℝ)) (ε : ℝ) (h : 0 < ε) : ℝ :=
  f.modulus (ε / 2) (half_pos h)

theorem δ_pos {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} : 0 < δ f ε h :=
  f.modulus_pos

/-- The set of points `k` so `k/n` is within `δ` of `x`.
-/
def s (f : C(I, ℝ)) (ε : ℝ) (h : 0 < ε) (n : ℕ) (x : I) : Finset (Finₓ (n + 1)) :=
  { k : Finₓ (n + 1) | dist k/ₙ x < δ f ε h }.toFinset

/-- If `k ∈ S`, then `f(k/n)` is close to `f x`.
-/
theorem lt_of_mem_S {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : Finₓ (n + 1)} (m : k ∈ s f ε h n x) :
    abs (f k/ₙ - f x) < ε / 2 := by
  apply f.dist_lt_of_dist_lt_modulus (ε / 2) (half_pos h)
  simpa [← S] using m

/-- If `k ∉ S`, then as `δ ≤ |x - k/n|`, we have the inequality `1 ≤ δ^-2 * (x - k/n)^2`.
This particular formulation will be helpful later.
-/
theorem le_of_mem_S_compl {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : Finₓ (n + 1)} (m : k ∈ s f ε h n xᶜ) :
    (1 : ℝ) ≤ δ f ε h ^ (-2 : ℤ) * (x - k/ₙ) ^ 2 := by
  simp only [← Finset.mem_compl, ← not_ltₓ, ← Set.mem_to_finset, ← Set.mem_set_of_eq, ← S] at m
  erw [zpow_neg, ← div_eq_inv_mul, one_le_div (pow_pos δ_pos 2), sq_le_sq, abs_of_pos δ_pos]
  rwa [dist_comm] at m

end bernsteinApproximation

open bernsteinApproximation

open BoundedContinuousFunction

open Filter

open TopologicalSpace

/-- The Bernstein approximations
```
∑ k : fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k)
```
for a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` tends to infinity.

This is the proof given in [Richard Beals' *Analysis, an introduction*][beals-analysis], §7D,
and reproduced on wikipedia.
-/
theorem bernstein_approximation_uniform (f : C(I, ℝ)) : Tendsto (fun n : ℕ => bernsteinApproximation n f) atTop (𝓝 f) :=
  by
  simp only [← metric.nhds_basis_ball.tendsto_right_iff, ← Metric.mem_ball, ← dist_eq_norm]
  intro ε h
  let δ := δ f ε h
  have nhds_zero := tendsto_const_div_at_top_nhds_0_nat (2 * ∥f∥ * δ ^ (-2 : ℤ))
  filter_upwards [nhds_zero.eventually (gt_mem_nhds (half_pos h)), eventually_gt_at_top 0] with n nh npos'
  have npos : 0 < (n : ℝ) := by
    exact_mod_cast npos'
  -- Two easy inequalities we'll need later:
  have w₁ : 0 ≤ 2 * ∥f∥ :=
    mul_nonneg
      (by
        norm_num)
      (norm_nonneg f)
  have w₂ : 0 ≤ 2 * ∥f∥ * δ ^ (-2 : ℤ) := mul_nonneg w₁ pow_minus_two_nonneg
  -- As `[0,1]` is compact, it suffices to check the inequality pointwise.
  rw [ContinuousMap.norm_lt_iff _ h]
  intro x
  -- The idea is to split up the sum over `k` into two sets,
  -- `S`, where `x - k/n < δ`, and its complement.
  let S := S f ε h n x
  calc abs ((bernsteinApproximation n f - f) x) = abs (bernsteinApproximation n f x - f x) :=
      rfl _ = abs (bernsteinApproximation n f x - f x * 1) := by
      rw [mul_oneₓ]_ = abs (bernsteinApproximation n f x - f x * ∑ k : Finₓ (n + 1), bernstein n k x) := by
      rw [bernstein.probability]_ = abs (∑ k : Finₓ (n + 1), (f k/ₙ - f x) * bernstein n k x) := by
      simp [← bernsteinApproximation, ← Finset.mul_sum, ←
        sub_mul]_ ≤ ∑ k : Finₓ (n + 1), abs ((f k/ₙ - f x) * bernstein n k x) :=
      Finset.abs_sum_le_sum_abs _ _ _ = ∑ k : Finₓ (n + 1), abs (f k/ₙ - f x) * bernstein n k x := by
      simp_rw [abs_mul,
        abs_eq_self.mpr
          bernstein_nonneg]_ =
        (∑ k in S, abs (f k/ₙ - f x) * bernstein n k x) + ∑ k in Sᶜ, abs (f k/ₙ - f x) * bernstein n k x :=
      (S.sum_add_sum_compl _).symm-- We'll now deal with the terms in `S` and the terms in `Sᶜ` in separate calc blocks.
        _ <
        ε / 2 + ε / 2 :=
      add_lt_add_of_le_of_lt _ _ _ = ε := add_halves ε
  · -- We now work on the terms in `S`: uniform continuity and `bernstein.probability`
    -- quickly give us a bound.
    calc (∑ k in S, abs (f k/ₙ - f x) * bernstein n k x) ≤ ∑ k in S, ε / 2 * bernstein n k x :=
        Finset.sum_le_sum fun k m =>
          mul_le_mul_of_nonneg_right (le_of_ltₓ (lt_of_mem_S m))
            bernstein_nonneg _ = ε / 2 * ∑ k in S, bernstein n k x :=
        by
        rw [Finset.mul_sum]-- In this step we increase the sum over `S` back to a sum over all of `fin (n+1)`,
          -- so that we can use `bernstein.probability`.
          _ ≤
          ε / 2 * ∑ k : Finₓ (n + 1), bernstein n k x :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_univ_sum_of_nonneg fun k => bernstein_nonneg)
          (le_of_ltₓ (half_pos h))_ = ε / 2 :=
        by
        rw [bernstein.probability, mul_oneₓ]
    
  · -- We now turn to working on `Sᶜ`: we control the difference term just using `∥f∥`,
    -- and then insert a `δ^(-2) * (x - k/n)^2` factor
    -- (which is at least one because we are not in `S`).
    calc (∑ k in Sᶜ, abs (f k/ₙ - f x) * bernstein n k x) ≤ ∑ k in Sᶜ, 2 * ∥f∥ * bernstein n k x :=
        Finset.sum_le_sum fun k m =>
          mul_le_mul_of_nonneg_right (f.dist_le_two_norm _ _)
            bernstein_nonneg _ = 2 * ∥f∥ * ∑ k in Sᶜ, bernstein n k x :=
        by
        rw [Finset.mul_sum]_ ≤ 2 * ∥f∥ * ∑ k in Sᶜ, δ ^ (-2 : ℤ) * (x - k/ₙ) ^ 2 * bernstein n k x :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun k m => by
            conv_lhs => rw [← one_mulₓ (bernstein _ _ _)]
            exact mul_le_mul_of_nonneg_right (le_of_mem_S_compl m) bernstein_nonneg)
          w₁-- Again enlarging the sum from `Sᶜ` to all of `fin (n+1)`
          _ ≤
          2 * ∥f∥ * ∑ k : Finₓ (n + 1), δ ^ (-2 : ℤ) * (x - k/ₙ) ^ 2 * bernstein n k x :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_univ_sum_of_nonneg fun k =>
            mul_nonneg (mul_nonneg pow_minus_two_nonneg (sq_nonneg _)) bernstein_nonneg)
          w₁ _ = 2 * ∥f∥ * δ ^ (-2 : ℤ) * ∑ k : Finₓ (n + 1), (x - k/ₙ) ^ 2 * bernstein n k x :=
        by
        conv_rhs =>
          rw [mul_assoc,
            Finset.mul_sum]simp only [mul_assoc]-- `bernstein.variance` and `x ∈ [0,1]` gives the uniform bound
          _ =
          2 * ∥f∥ * δ ^ (-2 : ℤ) * x * (1 - x) / n :=
        by
        rw [variance npos]
        ring _ ≤ 2 * ∥f∥ * δ ^ (-2 : ℤ) / n :=
        (div_le_div_right npos).mpr
          (by
            apply mul_nonneg_le_one_le w₂
            apply mul_nonneg_le_one_le w₂ le_rfl
            all_goals
              unit_interval)_ < ε / 2 :=
        nh
    

