/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Analysis.SpecialFunctions.Pow
import Mathbin.NumberTheory.Liouville.Basic
import Mathbin.Topology.Instances.Irrational

/-!
# Liouville numbers with a given exponent

We say that a real number `x` is a Liouville number with exponent `p : ℝ` if there exists a real
number `C` such that for infinitely many denominators `n` there exists a numerator `m` such that
`x ≠ m / n` and `|x - m / n| < C / n ^ p`. A number is a Liouville number in the sense of
`liouville` if it is `liouville_with` any real exponent, see `forall_liouville_with_iff`.

* If `p ≤ 1`, then this condition is trivial.

* If `1 < p ≤ 2`, then this condition is equivalent to `irrational x`. The forward implication
  does not require `p ≤ 2` and is formalized as `liouville_with.irrational`; the other implication
  follows from approximations by continued fractions and is not formalized yet.

* If `p > 2`, then this is a non-trivial condition on irrational numbers. In particular,
  [Thue–Siegel–Roth theorem](https://en.wikipedia.org/wiki/Roth's_theorem) states that such numbers
  must be transcendental.

In this file we define the predicate `liouville_with` and prove some basic facts about this
predicate.

## Tags

Liouville number, irrational, irrationality exponent
-/


open Filter Metric Real Set

open Filter TopologicalSpace

/-- We say that a real number `x` is a Liouville number with exponent `p : ℝ` if there exists a real
number `C` such that for infinitely many denominators `n` there exists a numerator `m` such that
`x ≠ m / n` and `|x - m / n| < C / n ^ p`.

A number is a Liouville number in the sense of `liouville` if it is `liouville_with` any real
exponent. -/
def LiouvilleWith (p x : ℝ) : Prop :=
  ∃ C, ∃ᶠ n : ℕ in at_top, ∃ m : ℤ, x ≠ m / n ∧ abs (x - m / n) < C / n ^ p

/-- For `p = 1` (hence, for any `p ≤ 1`), the condition `liouville_with p x` is trivial. -/
theorem liouville_with_one (x : ℝ) : LiouvilleWith 1 x := by
  use 2
  refine' ((eventually_gt_at_top 0).mono fun n hn => _).Frequently
  have hn' : (0 : ℝ) < n := by
    simpa
  have : x < ↑(⌊x * ↑n⌋ + 1) / ↑n := by
    rw [lt_div_iff hn', Int.cast_add, Int.cast_oneₓ]
    exact Int.lt_floor_add_one _
  refine' ⟨⌊x * n⌋ + 1, this.ne, _⟩
  rw [abs_sub_comm, abs_of_pos (sub_pos.2 this), rpow_one, sub_lt_iff_lt_add', add_div_eq_mul_add_div _ _ hn'.ne',
    div_lt_div_right hn']
  simpa [← bit0, add_assocₓ] using (Int.floor_le (x * n)).trans_lt (lt_add_one _)

namespace LiouvilleWith

variable {p q x y : ℝ} {r : ℚ} {m : ℤ} {n : ℕ}

/-- The constant `C` provided by the definition of `liouville_with` can be made positive.
We also add `1 ≤ n` to the list of assumptions about the denominator. While it is equivalent to
the original statement, the case `n = 0` breaks many arguments. -/
theorem exists_pos (h : LiouvilleWith p x) :
    ∃ (C : ℝ)(h₀ : 0 < C), ∃ᶠ n : ℕ in at_top, 1 ≤ n ∧ ∃ m : ℤ, x ≠ m / n ∧ abs (x - m / n) < C / n ^ p := by
  rcases h with ⟨C, hC⟩
  refine' ⟨max C 1, zero_lt_one.trans_le <| le_max_rightₓ _ _, _⟩
  refine' ((eventually_ge_at_top 1).and_frequently hC).mono _
  rintro n ⟨hle, m, hne, hlt⟩
  refine' ⟨hle, m, hne, hlt.trans_le _⟩
  exact div_le_div_of_le (rpow_nonneg_of_nonneg n.cast_nonneg _) (le_max_leftₓ _ _)

/-- If a number is Liouville with exponent `p`, then it is Liouville with any smaller exponent. -/
theorem mono (h : LiouvilleWith p x) (hle : q ≤ p) : LiouvilleWith q x := by
  rcases h.exists_pos with ⟨C, hC₀, hC⟩
  refine' ⟨C, hC.mono _⟩
  rintro n ⟨hn, m, hne, hlt⟩
  refine' ⟨m, hne, hlt.trans_le <| div_le_div_of_le_left hC₀.le _ _⟩
  exacts[rpow_pos_of_pos (Nat.cast_pos.2 hn) _, rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) hle]

/-- If `x` satisfies Liouville condition with exponent `p` and `q < p`, then `x`
satisfies Liouville condition with exponent `q` and constant `1`. -/
theorem frequently_lt_rpow_neg (h : LiouvilleWith p x) (hlt : q < p) :
    ∃ᶠ n : ℕ in at_top, ∃ m : ℤ, x ≠ m / n ∧ abs (x - m / n) < n ^ -q := by
  rcases h.exists_pos with ⟨C, hC₀, hC⟩
  have : ∀ᶠ n : ℕ in at_top, C < n ^ (p - q) := by
    simpa only [← (· ∘ ·), ← neg_sub, ← one_div] using
      ((tendsto_rpow_at_top (sub_pos.2 hlt)).comp tendsto_coe_nat_at_top_at_top).Eventually (eventually_gt_at_top C)
  refine' (this.and_frequently hC).mono _
  rintro n ⟨hnC, hn, m, hne, hlt⟩
  replace hn : (0 : ℝ) < n := Nat.cast_pos.2 hn
  refine' ⟨m, hne, hlt.trans <| (div_lt_iff <| rpow_pos_of_pos hn _).2 _⟩
  rwa [mul_comm, ← rpow_add hn, ← sub_eq_add_neg]

/-- The product of a Liouville number and a nonzero rational number is again a Liouville number.  -/
theorem mul_rat (h : LiouvilleWith p x) (hr : r ≠ 0) : LiouvilleWith p (x * r) := by
  rcases h.exists_pos with ⟨C, hC₀, hC⟩
  refine' ⟨r.denom ^ p * (abs r * C), (tendsto_id.nsmul_at_top r.pos).Frequently (hC.mono _)⟩
  rintro n ⟨hn, m, hne, hlt⟩
  have A : (↑(r.num * m) : ℝ) / ↑(r.denom • id n) = m / n * r := by
    simp [div_mul_div_comm, r.cast_def, ← mul_comm]
  refine' ⟨r.num * m, _, _⟩
  · rw [A]
    simp [← hne, ← hr]
    
  · rw [A, ← sub_mul, abs_mul]
    simp only [← smul_eq_mul, ← id.def, ← Nat.cast_mulₓ]
    refine' (mul_lt_mul_of_pos_right hlt <| abs_pos.2 <| Rat.cast_ne_zero.2 hr).trans_le _
    rw [mul_rpow, mul_div_mul_left, mul_comm, mul_div_assoc]
    exacts[(rpow_pos_of_pos (Nat.cast_pos.2 r.pos) _).ne', Nat.cast_nonneg _, Nat.cast_nonneg _]
    

/-- The product `x * r`, `r : ℚ`, `r ≠ 0`, is a Liouville number with exponent `p` if and only if
`x` satisfies the same condition. -/
theorem mul_rat_iff (hr : r ≠ 0) : LiouvilleWith p (x * r) ↔ LiouvilleWith p x :=
  ⟨fun h => by
    simpa only [← mul_assoc, Rat.cast_mul, ← mul_inv_cancel hr, ← Rat.cast_one, ← mul_oneₓ] using
      h.mul_rat (inv_ne_zero hr),
    fun h => h.mul_rat hr⟩

/-- The product `r * x`, `r : ℚ`, `r ≠ 0`, is a Liouville number with exponent `p` if and only if
`x` satisfies the same condition. -/
theorem rat_mul_iff (hr : r ≠ 0) : LiouvilleWith p (r * x) ↔ LiouvilleWith p x := by
  rw [mul_comm, mul_rat_iff hr]

theorem rat_mul (h : LiouvilleWith p x) (hr : r ≠ 0) : LiouvilleWith p (r * x) :=
  (rat_mul_iff hr).2 h

theorem mul_int_iff (hm : m ≠ 0) : LiouvilleWith p (x * m) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_coe_int, mul_rat_iff (Int.cast_ne_zero.2 hm)]

theorem mul_int (h : LiouvilleWith p x) (hm : m ≠ 0) : LiouvilleWith p (x * m) :=
  (mul_int_iff hm).2 h

theorem int_mul_iff (hm : m ≠ 0) : LiouvilleWith p (m * x) ↔ LiouvilleWith p x := by
  rw [mul_comm, mul_int_iff hm]

theorem int_mul (h : LiouvilleWith p x) (hm : m ≠ 0) : LiouvilleWith p (m * x) :=
  (int_mul_iff hm).2 h

theorem mul_nat_iff (hn : n ≠ 0) : LiouvilleWith p (x * n) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_coe_nat, mul_rat_iff (Nat.cast_ne_zero.2 hn)]

theorem mul_nat (h : LiouvilleWith p x) (hn : n ≠ 0) : LiouvilleWith p (x * n) :=
  (mul_nat_iff hn).2 h

theorem nat_mul_iff (hn : n ≠ 0) : LiouvilleWith p (n * x) ↔ LiouvilleWith p x := by
  rw [mul_comm, mul_nat_iff hn]

theorem nat_mul (h : LiouvilleWith p x) (hn : n ≠ 0) : LiouvilleWith p (n * x) := by
  rw [mul_comm]
  exact h.mul_nat hn

theorem add_rat (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (x + r) := by
  rcases h.exists_pos with ⟨C, hC₀, hC⟩
  refine' ⟨r.denom ^ p * C, (tendsto_id.nsmul_at_top r.pos).Frequently (hC.mono _)⟩
  rintro n ⟨hn, m, hne, hlt⟩
  have hr : (0 : ℝ) < r.denom := Nat.cast_pos.2 r.pos
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (zero_lt_one.trans_le hn).ne'
  have : (↑(r.denom * m + r.num * n : ℤ) / ↑(r.denom • id n) : ℝ) = m / n + r := by
    simp [← add_div, ← hr.ne', ← mul_div_mul_left, ← mul_div_mul_right, ← hn', Rat.cast_def]
  refine' ⟨r.denom * m + r.num * n, _⟩
  rw [this, add_sub_add_right_eq_sub]
  refine'
    ⟨by
      simpa, hlt.trans_le (le_of_eqₓ _)⟩
  have : (r.denom ^ p : ℝ) ≠ 0 := (rpow_pos_of_pos hr _).ne'
  simp [← mul_rpow, ← Nat.cast_nonneg, ← mul_div_mul_left, ← this]

@[simp]
theorem add_rat_iff : LiouvilleWith p (x + r) ↔ LiouvilleWith p x :=
  ⟨fun h => by
    simpa using h.add_rat (-r), fun h => h.add_rat r⟩

@[simp]
theorem rat_add_iff : LiouvilleWith p (r + x) ↔ LiouvilleWith p x := by
  rw [add_commₓ, add_rat_iff]

theorem rat_add (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (r + x) :=
  add_commₓ x r ▸ h.add_rat r

@[simp]
theorem add_int_iff : LiouvilleWith p (x + m) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_coe_int m, add_rat_iff]

@[simp]
theorem int_add_iff : LiouvilleWith p (m + x) ↔ LiouvilleWith p x := by
  rw [add_commₓ, add_int_iff]

@[simp]
theorem add_nat_iff : LiouvilleWith p (x + n) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_coe_nat n, add_rat_iff]

@[simp]
theorem nat_add_iff : LiouvilleWith p (n + x) ↔ LiouvilleWith p x := by
  rw [add_commₓ, add_nat_iff]

theorem add_int (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (x + m) :=
  add_int_iff.2 h

theorem int_add (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (m + x) :=
  int_add_iff.2 h

theorem add_nat (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (x + n) :=
  h.add_int n

theorem nat_add (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (n + x) :=
  h.int_add n

protected theorem neg (h : LiouvilleWith p x) : LiouvilleWith p (-x) := by
  rcases h with ⟨C, hC⟩
  refine' ⟨C, hC.mono _⟩
  rintro n ⟨m, hne, hlt⟩
  use -m
  simp [← neg_div, ← abs_sub_comm _ x, *]

@[simp]
theorem neg_iff : LiouvilleWith p (-x) ↔ LiouvilleWith p x :=
  ⟨fun h => neg_negₓ x ▸ h.neg, LiouvilleWith.neg⟩

@[simp]
theorem sub_rat_iff : LiouvilleWith p (x - r) ↔ LiouvilleWith p x := by
  rw [sub_eq_add_neg, ← Rat.cast_neg, add_rat_iff]

theorem sub_rat (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (x - r) :=
  sub_rat_iff.2 h

@[simp]
theorem sub_int_iff : LiouvilleWith p (x - m) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_coe_int, sub_rat_iff]

theorem sub_int (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (x - m) :=
  sub_int_iff.2 h

@[simp]
theorem sub_nat_iff : LiouvilleWith p (x - n) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_coe_nat, sub_rat_iff]

theorem sub_nat (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (x - n) :=
  sub_nat_iff.2 h

@[simp]
theorem rat_sub_iff : LiouvilleWith p (r - x) ↔ LiouvilleWith p x := by
  simp [← sub_eq_add_neg]

theorem rat_sub (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (r - x) :=
  rat_sub_iff.2 h

@[simp]
theorem int_sub_iff : LiouvilleWith p (m - x) ↔ LiouvilleWith p x := by
  simp [← sub_eq_add_neg]

theorem int_sub (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (m - x) :=
  int_sub_iff.2 h

@[simp]
theorem nat_sub_iff : LiouvilleWith p (n - x) ↔ LiouvilleWith p x := by
  simp [← sub_eq_add_neg]

theorem nat_sub (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (n - x) :=
  nat_sub_iff.2 h

theorem ne_cast_int (h : LiouvilleWith p x) (hp : 1 < p) (m : ℤ) : x ≠ m := by
  rintro rfl
  rename' m => M
  rcases((eventually_gt_at_top 0).and_frequently (h.frequently_lt_rpow_neg hp)).exists with
    ⟨n : ℕ, hn : 0 < n, m : ℤ, hne : (M : ℝ) ≠ m / n, hlt : abs (M - m / n : ℝ) < n ^ (-1 : ℝ)⟩
  refine' hlt.not_le _
  have hn' : (0 : ℝ) < n := by
    simpa
  rw [rpow_neg_one, ← one_div, sub_div' _ _ _ hn'.ne', abs_div, Nat.abs_cast, div_le_div_right hn']
  norm_cast
  rw [← zero_addₓ (1 : ℤ), Int.add_one_le_iff, abs_pos, sub_ne_zero]
  rw [Ne.def, eq_div_iff hn'.ne'] at hne
  exact_mod_cast hne

/-- A number satisfying the Liouville condition with exponent `p > 1` is an irrational number. -/
protected theorem irrational (h : LiouvilleWith p x) (hp : 1 < p) : Irrational x := by
  rintro ⟨r, rfl⟩
  rcases eq_or_ne r 0 with (rfl | h0)
  · refine' h.ne_cast_int hp 0 _
    rw [Rat.cast_zero, Int.cast_zeroₓ]
    
  · refine' (h.mul_rat (inv_ne_zero h0)).ne_cast_int hp 1 _
    simp [← Rat.cast_ne_zero.2 h0]
    

end LiouvilleWith

namespace Liouville

variable {x : ℝ}

/-- If `x` is a Liouville number, then for any `n`, for infinitely many denominators `b` there
exists a numerator `a` such that `x ≠ a / b` and `|x - a / b| < 1 / b ^ n`. -/
theorem frequently_exists_num (hx : Liouville x) (n : ℕ) :
    ∃ᶠ b : ℕ in at_top, ∃ a : ℤ, x ≠ a / b ∧ abs (x - a / b) < 1 / b ^ n := by
  refine' not_not.1 fun H => _
  simp only [← Liouville, ← not_forall, ← not_exists, ← not_frequently, ← not_and, ← not_ltₓ, ← eventually_at_top] at H
  rcases H with ⟨N, hN⟩
  have : ∀, ∀ b > (1 : ℕ), ∀, ∀ᶠ m : ℕ in at_top, ∀ a : ℤ, (1 / b ^ m : ℝ) ≤ abs (x - a / b) := by
    intro b hb
    have hb0' : (b : ℚ) ≠ 0 := (zero_lt_one.trans (Nat.one_lt_cast.2 hb)).ne'
    replace hb : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    have hb0 : (0 : ℝ) < b := zero_lt_one.trans hb
    have H : tendsto (fun m => 1 / b ^ m : ℕ → ℝ) at_top (𝓝 0) := by
      simp only [← one_div]
      exact tendsto_inv_at_top_zero.comp (tendsto_pow_at_top_at_top_of_one_lt hb)
    refine' (H.eventually (hx.irrational.eventually_forall_le_dist_cast_div b)).mono _
    exact fun m hm a => hm a
  have : ∀ᶠ m : ℕ in at_top, ∀, ∀ b < N, ∀, 1 < b → ∀ a : ℤ, (1 / b ^ m : ℝ) ≤ abs (x - a / b) :=
    (finite_lt_nat N).eventually_all.2 fun b hb => eventually_imp_distrib_left.2 (this b)
  rcases(this.and (eventually_ge_at_top n)).exists with ⟨m, hm, hnm⟩
  rcases hx m with ⟨a, b, hb, hne, hlt⟩
  lift b to ℕ using zero_le_one.trans hb.le
  norm_cast  at hb
  push_cast at hne hlt
  cases le_or_ltₓ N b
  · refine' (hN b h a hne).not_lt (hlt.trans_le _)
    replace hb : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    have hb0 : (0 : ℝ) < b := zero_lt_one.trans hb
    exact one_div_le_one_div_of_le (pow_pos hb0 _) (pow_le_pow hb.le hnm)
    
  · exact (hm b h hb _).not_lt hlt
    

/-- A Liouville number is a Liouville number with any real exponent. -/
protected theorem liouville_with (hx : Liouville x) (p : ℝ) : LiouvilleWith p x := by
  suffices : LiouvilleWith ⌈p⌉₊ x
  exact this.mono (Nat.le_ceil p)
  refine' ⟨1, ((eventually_gt_at_top 1).and_frequently (hx.frequently_exists_num ⌈p⌉₊)).mono _⟩
  rintro b ⟨hb, a, hne, hlt⟩
  refine' ⟨a, hne, _⟩
  rwa [rpow_nat_cast]

end Liouville

/-- A number satisfies the Liouville condition with any exponent if and only if it is a Liouville
number. -/
theorem forall_liouville_with_iff {x : ℝ} : (∀ p, LiouvilleWith p x) ↔ Liouville x := by
  refine' ⟨fun H n => _, Liouville.liouville_with⟩
  rcases((eventually_gt_at_top 1).and_frequently ((H (n + 1)).frequently_lt_rpow_neg (lt_add_one n))).exists with
    ⟨b, hb, a, hne, hlt⟩
  exact
    ⟨a, b, by
      exact_mod_cast hb, hne, by
      simpa [← rpow_neg] using hlt⟩

