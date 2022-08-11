/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Jujian Zhang
-/
import Mathbin.NumberTheory.Liouville.Basic

/-!

# Liouville constants

This file contains a construction of a family of Liouville numbers, indexed by a natural number $m$.
The most important property is that they are examples of transcendental real numbers.
This fact is recorded in `liouville.is_transcendental`.

More precisely, for a real number $m$, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for $1 < m$.  However, there is no restriction on $m$, since,
if the series does not converge, then the sum of the series is defined to be zero.

We prove that, for $m \in \mathbb{N}$ satisfying $2 \le m$, Liouville's constant associated to $m$
is a transcendental number.  Classically, the Liouville number for $m = 2$ is the one called
``Liouville's constant''.

## Implementation notes

The indexing $m$ is eventually a natural number satisfying $2 ≤ m$.  However, we prove the first few
lemmas for $m \in \mathbb{R}$.
-/


noncomputable section

open Nat BigOperators

open Real Finset

namespace Liouville

/-- For a real number `m`, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for `1 < m`.  However, there is no restriction on `m`, since,
if the series does not converge, then the sum of the series is defined to be zero.
-/
def liouvilleNumber (m : ℝ) : ℝ :=
  ∑' i : ℕ, 1 / m ^ i !

/-- `liouville_number_initial_terms` is the sum of the first `k + 1` terms of Liouville's constant,
i.e.
$$
\sum_{i=0}^k\frac{1}{m^{i!}}.
$$
-/
def liouvilleNumberInitialTerms (m : ℝ) (k : ℕ) : ℝ :=
  ∑ i in range (k + 1), 1 / m ^ i !

/-- `liouville_number_tail` is the sum of the series of the terms in `liouville_number m`
starting from `k+1`, i.e
$$
\sum_{i=k+1}^\infty\frac{1}{m^{i!}}.
$$
-/
def liouvilleNumberTail (m : ℝ) (k : ℕ) : ℝ :=
  ∑' i, 1 / m ^ (i + (k + 1))!

theorem liouville_number_tail_pos {m : ℝ} (hm : 1 < m) (k : ℕ) : 0 < liouvilleNumberTail m k :=
  calc
    -- replace `0` with the constantly zero series `∑ i : ℕ, 0`
        (0 : ℝ) =
        ∑' i : ℕ, 0 :=
      tsum_zero.symm
    _ < liouvilleNumberTail m k :=-- to show that a series with non-negative terms has strictly positive sum it suffices
          -- to prove that
          -- 1. the terms of the zero series are indeed non-negative
          -- 2. the terms of our series are non-negative
          -- 3. one term of our series is strictly positive -- they all are, we use the first term
          tsum_lt_tsum_of_nonneg
          (fun _ => rfl.le) (fun i => one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _))
          (one_div_pos.mpr
            (pow_pos (zero_lt_one.trans hm)
              (0 +
                  (k +
                    1))!)) <|-- 4. our series converges -- it does since it is the tail of a converging series, though
          -- this is not the argument here.
          summable_one_div_pow_of_le
          hm fun i => trans le_self_add (Nat.self_le_factorial _)
    

/-- Split the sum definining a Liouville number into the first `k` term and the rest. -/
theorem liouville_number_eq_initial_terms_add_tail {m : ℝ} (hm : 1 < m) (k : ℕ) :
    liouvilleNumber m = liouvilleNumberInitialTerms m k + liouvilleNumberTail m k :=
  (sum_add_tsum_nat_add _ (summable_one_div_pow_of_le hm fun i => i.self_le_factorial)).symm

/-! We now prove two useful inequalities, before collecting everything together. -/


/-- Partial inequality, works with `m ∈ ℝ` satisfying `1 < m`. -/
theorem tsum_one_div_pow_factorial_lt (n : ℕ) {m : ℝ} (m1 : 1 < m) :
    (∑' i : ℕ, 1 / m ^ (i + (n + 1))!) < (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) :=
  have
    m0 :-- two useful inequalities
      0 <
      m :=
    zero_lt_one.trans m1
  have mi : abs (1 / m) < 1 := (le_of_eqₓ (abs_of_pos (one_div_pos.mpr m0))).trans_lt ((div_lt_one m0).mpr m1)
  calc
    (∑' i, 1 / m ^ (i + (n + 1))!) <
        ∑' i, 1 / m ^ (i + (n + 1)!) :=-- to show the strict inequality between these series, we prove that:
        tsum_lt_tsum_of_nonneg
        (-- 1. the first series has non-negative terms
        fun b => one_div_nonneg.mpr (pow_nonneg m0.le _))
        (-- 2. the second series dominates the first
        fun b => one_div_pow_le_one_div_pow_of_le m1.le (b.add_factorial_succ_le_factorial_add_succ n))
        (-- 3. the term with index `i = 2` of the first series is strictly smaller than
          -- the corresponding term of the second series
          one_div_pow_strict_anti
          m1 (n.add_factorial_succ_lt_factorial_add_succ rfl.le))
        (-- 4. the second series is summable, since its terms grow quickly
          summable_one_div_pow_of_le
          m1 fun j => Nat.Le.intro rfl)
    _ = ∑' i, (1 / m) ^ i * (1 / m ^ (n + 1)!) :=-- split the sum in the exponent and massage
    by
      congr
      ext i
      rw [pow_addₓ, ← div_div, div_eq_mul_one_div, one_div_pow]
    -- factor the constant `(1 / m ^ (n + 1)!)` out of the series
        _ =
        (∑' i, (1 / m) ^ i) * (1 / m ^ (n + 1)!) :=
      tsum_mul_right
    _ = (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) :=-- the series if the geometric series
          mul_eq_mul_right_iff.mpr
        (Or.inl (tsum_geometric_of_abs_lt_1 mi))
    

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
theorem aux_calc (n : ℕ) {m : ℝ} (hm : 2 ≤ m) : (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) ≤ 1 / (m ^ n !) ^ n :=
  calc
    (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) ≤ 2 * (1 / m ^ (n + 1)!) :=-- the second factors coincide (and are non-negative),
        -- the first factors, satisfy the inequality `sub_one_div_inv_le_two`
        mul_mono_nonneg
        (one_div_nonneg.mpr (pow_nonneg (zero_le_two.trans hm) _)) (sub_one_div_inv_le_two hm)
    _ = 2 / m ^ (n + 1)! := mul_one_div 2 _
    _ = 2 / m ^ (n ! * (n + 1)) := congr_arg ((· / ·) 2) (congr_arg (pow m) (mul_comm _ _))
    _ ≤ 1 / m ^ (n ! * n) := by
      -- [ NB: in this block, I do not follow the brace convention for subgoals -- I wait until
      --   I solve all extraneous goals at once with `exact pow_pos (zero_lt_two.trans_le hm) _`. ]
      -- Clear denominators and massage*
      apply (div_le_div_iff _ _).mpr
      conv_rhs => rw [one_mulₓ, mul_addₓ, pow_addₓ, mul_oneₓ, pow_mulₓ, mul_comm, ← pow_mulₓ]
      -- the second factors coincide, so we prove the inequality of the first factors*
      apply (mul_le_mul_right _).mpr
      any_goals {
      }
      -- `2 ≤ m ^ n!` is a consequence of monotonicity of exponentiation at `2 ≤ m`.
      exact trans (trans hm (pow_oneₓ _).symm.le) (pow_mono (one_le_two.trans hm) n.factorial_pos)
    _ = 1 / (m ^ n !) ^ n := congr_arg ((· / ·) 1) (pow_mulₓ m n ! n)
    

/-!  Starting from here, we specialize to the case in which `m` is a natural number. -/


/-- The sum of the `k` initial terms of the Liouville number to base `m` is a ratio of natural
numbers where the denominator is `m ^ k!`. -/
theorem liouville_number_rat_initial_terms {m : ℕ} (hm : 0 < m) (k : ℕ) :
    ∃ p : ℕ, liouvilleNumberInitialTerms m k = p / m ^ k ! := by
  induction' k with k h
  · exact
      ⟨1, by
        rw [liouville_number_initial_terms, range_one, sum_singleton, Nat.cast_oneₓ]⟩
    
  · rcases h with ⟨p_k, h_k⟩
    use p_k * m ^ ((k + 1)! - k !) + 1
    unfold liouville_number_initial_terms  at h_k⊢
    rw [sum_range_succ, h_k, div_add_div, div_eq_div_iff, add_mulₓ]
    · norm_cast
      rw [add_mulₓ, one_mulₓ, Nat.factorial_succ,
        show k.succ * k ! - k ! = (k.succ - 1) * k ! by
          rw [tsub_mul, one_mulₓ],
        Nat.succ_sub_one, add_mulₓ, one_mulₓ, pow_addₓ]
      simp [← mul_assoc]
      
    refine' mul_ne_zero_iff.mpr ⟨_, _⟩
    all_goals
      exact pow_ne_zero _ (nat.cast_ne_zero.mpr hm.ne.symm)
    

theorem is_liouville {m : ℕ} (hm : 2 ≤ m) : Liouville (liouvilleNumber m) := by
  -- two useful inequalities
  have mZ1 : 1 < (m : ℤ) := by
    norm_cast
    exact one_lt_two.trans_le hm
  have m1 : 1 < (m : ℝ) := by
    norm_cast
    exact one_lt_two.trans_le hm
  intro n
  -- the first `n` terms sum to `p / m ^ k!`
  rcases liouville_number_rat_initial_terms (zero_lt_two.trans_le hm) n with ⟨p, hp⟩
  refine' ⟨p, m ^ n !, one_lt_pow mZ1 n.factorial_ne_zero, _⟩
  push_cast
  -- separate out the sum of the first `n` terms and the rest
  rw [liouville_number_eq_initial_terms_add_tail m1 n, ← hp, add_sub_cancel',
    abs_of_nonneg (liouville_number_tail_pos m1 _).le]
  exact
    ⟨((lt_add_iff_pos_right _).mpr (liouville_number_tail_pos m1 n)).Ne.symm,
      (tsum_one_div_pow_factorial_lt n m1).trans_le (aux_calc _ (nat.cast_two.symm.le.trans (nat.cast_le.mpr hm)))⟩

/- Placing this lemma outside of the `open/closed liouville`-namespace would allow to remove
`_root_.`, at the cost of some other small weirdness. -/
theorem is_transcendental {m : ℕ} (hm : 2 ≤ m) : Transcendental ℤ (liouvilleNumber m) :=
  transcendental (is_liouville hm)

end Liouville

