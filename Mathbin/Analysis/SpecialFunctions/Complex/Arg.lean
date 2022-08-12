/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The argument of a complex number.

We define `arg : ℂ → ℝ`, returing a real number in the range (-π, π],
such that for `x ≠ 0`, `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
while `arg 0` defaults to `0`
-/


noncomputable section

namespace Complex

open ComplexConjugate Real TopologicalSpace

open Filter Set

/-- `arg` returns values in the range (-π, π], such that for `x ≠ 0`,
  `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
  `arg 0` defaults to `0` -/
noncomputable def arg (x : ℂ) : ℝ :=
  if 0 ≤ x.re then Real.arcsin (x.im / x.abs)
  else if 0 ≤ x.im then Real.arcsin ((-x).im / x.abs) + π else Real.arcsin ((-x).im / x.abs) - π

theorem sin_arg (x : ℂ) : Real.sin (arg x) = x.im / x.abs := by
  unfold arg <;>
    split_ifs <;>
      simp [← sub_eq_add_neg, ← arg, ←
        Real.sin_arcsin (abs_le.1 (abs_im_div_abs_le_one x)).1 (abs_le.1 (abs_im_div_abs_le_one x)).2, ← Real.sin_add, ←
        neg_div, ← Real.arcsin_neg, ← Real.sin_neg]

theorem cos_arg {x : ℂ} (hx : x ≠ 0) : Real.cos (arg x) = x.re / x.abs := by
  have habs : 0 < abs x := abs_pos.2 hx
  have him : abs (im x / abs x) ≤ 1 := by
    rw [_root_.abs_div, abs_abs]
    exact div_le_one_of_le x.abs_im_le_abs x.abs_nonneg
  rw [abs_le] at him
  rw [arg]
  split_ifs with h₁ h₂ h₂
  · rw [Real.cos_arcsin] <;> field_simp [← Real.sqrt_sq, ← habs.le, *]
    
  · rw [Real.cos_add_pi, Real.cos_arcsin]
    · field_simp [← Real.sqrt_div (sq_nonneg _), ← Real.sqrt_sq_eq_abs, ← _root_.abs_of_neg (not_leₓ.1 h₁), *]
      
    · simpa [← neg_div] using him.2
      
    · simpa [← neg_div, ← neg_le] using him.1
      
    
  · rw [Real.cos_sub_pi, Real.cos_arcsin]
    · field_simp [← Real.sqrt_div (sq_nonneg _), ← Real.sqrt_sq_eq_abs, ← _root_.abs_of_neg (not_leₓ.1 h₁), *]
      
    · simpa [← neg_div] using him.2
      
    · simpa [← neg_div, ← neg_le] using him.1
      
    

@[simp]
theorem abs_mul_exp_arg_mul_I (x : ℂ) : ↑(abs x) * exp (arg x * I) = x := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
    
  · have : abs x ≠ 0 := abs_ne_zero.2 hx
    ext <;> field_simp [← sin_arg, ← cos_arg hx, ← this, ← mul_comm (abs x)]
    

@[simp]
theorem abs_mul_cos_add_sin_mul_I (x : ℂ) : (abs x * (cos (arg x) + sin (arg x) * I) : ℂ) = x := by
  rw [← exp_mul_I, abs_mul_exp_arg_mul_I]

theorem abs_eq_one_iff (z : ℂ) : abs z = 1 ↔ ∃ θ : ℝ, exp (θ * I) = z := by
  refine' ⟨fun hz => ⟨arg z, _⟩, _⟩
  · calc exp (arg z * I) = abs z * exp (arg z * I) := by
        rw [hz, of_real_one, one_mulₓ]_ = z := abs_mul_exp_arg_mul_I z
    
  · rintro ⟨θ, rfl⟩
    exact Complex.abs_exp_of_real_mul_I θ
    

@[simp]
theorem range_exp_mul_I : (Range fun x : ℝ => exp (x * I)) = Metric.Sphere 0 1 := by
  ext x
  simp only [← mem_sphere_zero_iff_norm, ← norm_eq_abs, ← abs_eq_one_iff, ← mem_range]

theorem arg_mul_cos_add_sin_mul_I {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : θ ∈ Ioc (-π) π) :
    arg (r * (cos θ + sin θ * I)) = θ := by
  have hπ := Real.pi_pos
  simp only [← arg, ← abs_mul, ← abs_cos_add_sin_mul_I, ← abs_of_nonneg hr.le, ← mul_oneₓ]
  simp only [← of_real_mul_re, ← of_real_mul_im, ← neg_im, of_real_cos, of_real_sin, mk_eq_add_mul_I, ← neg_div, ←
    mul_div_cancel_left _ hr.ne', ← mul_nonneg_iff_right_nonneg_of_pos hr]
  by_cases' h₁ : θ ∈ Icc (-(π / 2)) (π / 2)
  · rw [if_pos]
    exacts[Real.arcsin_sin' h₁, Real.cos_nonneg_of_mem_Icc h₁]
    
  · rw [mem_Icc, not_and_distrib, not_leₓ, not_leₓ] at h₁
    cases h₁
    · replace hθ := hθ.1
      have hcos : Real.cos θ < 0 := by
        rw [← neg_pos, ← Real.cos_add_pi]
        refine' Real.cos_pos_of_mem_Ioo ⟨_, _⟩ <;> linarith
      have hsin : Real.sin θ < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt
          (by
            linarith)
          hθ
      rw [if_neg, if_neg, ← Real.sin_add_pi, Real.arcsin_sin, add_sub_cancel] <;> [linarith, linarith,
        exact hsin.not_le, exact hcos.not_le]
      
    · replace hθ := hθ.2
      have hcos : Real.cos θ < 0 :=
        Real.cos_neg_of_pi_div_two_lt_of_lt h₁
          (by
            linarith)
      have hsin : 0 ≤ Real.sin θ :=
        Real.sin_nonneg_of_mem_Icc
          ⟨by
            linarith, hθ⟩
      rw [if_neg, if_pos, ← Real.sin_sub_pi, Real.arcsin_sin, sub_add_cancel] <;> [linarith, linarith, exact hsin,
        exact hcos.not_le]
      
    

theorem arg_cos_add_sin_mul_I {θ : ℝ} (hθ : θ ∈ Ioc (-π) π) : arg (cos θ + sin θ * I) = θ := by
  rw [← one_mulₓ (_ + _), ← of_real_one, arg_mul_cos_add_sin_mul_I zero_lt_one hθ]

@[simp]
theorem arg_zero : arg 0 = 0 := by
  simp [← arg, ← le_reflₓ]

theorem ext_abs_arg {x y : ℂ} (h₁ : x.abs = y.abs) (h₂ : x.arg = y.arg) : x = y := by
  rw [← abs_mul_exp_arg_mul_I x, ← abs_mul_exp_arg_mul_I y, h₁, h₂]

theorem ext_abs_arg_iff {x y : ℂ} : x = y ↔ abs x = abs y ∧ arg x = arg y :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, and_imp.2 ext_abs_arg⟩

theorem arg_mem_Ioc (z : ℂ) : arg z ∈ Ioc (-π) π := by
  have hπ : 0 < π := Real.pi_pos
  rcases eq_or_ne z 0 with (rfl | hz)
  simp [← hπ, ← hπ.le]
  rcases exists_unique_add_zsmul_mem_Ioc Real.two_pi_pos (arg z) (-π) with ⟨N, hN, -⟩
  rw [two_mul, neg_add_cancel_leftₓ, ← two_mul, zsmul_eq_mul] at hN
  rw [← abs_mul_cos_add_sin_mul_I z, ← cos_add_int_mul_two_pi _ N, ← sin_add_int_mul_two_pi _ N]
  simp only [of_real_one, of_real_bit0, of_real_mul, of_real_add, of_real_int_cast]
  rwa [arg_mul_cos_add_sin_mul_I (abs_pos.2 hz) hN]

@[simp]
theorem range_arg : Range arg = Ioc (-π) π :=
  (range_subset_iff.2 arg_mem_Ioc).antisymm fun x hx => ⟨_, arg_cos_add_sin_mul_I hx⟩

theorem arg_le_pi (x : ℂ) : arg x ≤ π :=
  (arg_mem_Ioc x).2

theorem neg_pi_lt_arg (x : ℂ) : -π < arg x :=
  (arg_mem_Ioc x).1

@[simp]
theorem arg_nonneg_iff {z : ℂ} : 0 ≤ arg z ↔ 0 ≤ z.im := by
  rcases eq_or_ne z 0 with (rfl | h₀)
  · simp
    
  calc 0 ≤ arg z ↔ 0 ≤ Real.sin (arg z) :=
      ⟨fun h => Real.sin_nonneg_of_mem_Icc ⟨h, arg_le_pi z⟩, by
        contrapose!
        intro h
        exact Real.sin_neg_of_neg_of_neg_pi_lt h (neg_pi_lt_arg _)⟩_ ↔ _ :=
      by
      rw [sin_arg, le_div_iff (abs_pos.2 h₀), zero_mul]

@[simp]
theorem arg_neg_iff {z : ℂ} : arg z < 0 ↔ z.im < 0 :=
  lt_iff_lt_of_le_iff_le arg_nonneg_iff

theorem arg_real_mul (x : ℂ) {r : ℝ} (hr : 0 < r) : arg (r * x) = arg x := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · rw [mul_zero]
    
  conv_lhs =>
    rw [← abs_mul_cos_add_sin_mul_I x, ← mul_assoc, ← of_real_mul,
      arg_mul_cos_add_sin_mul_I (mul_pos hr (abs_pos.2 hx)) x.arg_mem_Ioc]

theorem arg_eq_arg_iff {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) : arg x = arg y ↔ (abs y / abs x : ℂ) * x = y := by
  simp only [← ext_abs_arg_iff, ← abs_mul, ← abs_div, ← abs_of_real, ← abs_abs, ← div_mul_cancel _ (abs_ne_zero.2 hx), ←
    eq_self_iff_true, ← true_andₓ]
  rw [← of_real_div, arg_real_mul]
  exact div_pos (abs_pos.2 hy) (abs_pos.2 hx)

@[simp]
theorem arg_one : arg 1 = 0 := by
  simp [← arg, ← zero_le_one]

@[simp]
theorem arg_neg_one : arg (-1) = π := by
  simp [← arg, ← le_reflₓ, ← not_leₓ.2 (@zero_lt_one ℝ _ _)]

@[simp]
theorem arg_I : arg i = π / 2 := by
  simp [← arg, ← le_reflₓ]

@[simp]
theorem arg_neg_I : arg (-I) = -(π / 2) := by
  simp [← arg, ← le_reflₓ]

@[simp]
theorem tan_arg (x : ℂ) : Real.tan (arg x) = x.im / x.re := by
  by_cases' h : x = 0
  · simp only [← h, ← zero_div, ← Complex.zero_im, ← Complex.arg_zero, ← Real.tan_zero, ← Complex.zero_re]
    
  rw [Real.tan_eq_sin_div_cos, sin_arg, cos_arg h, div_div_div_cancel_right _ (abs_ne_zero.2 h)]

theorem arg_of_real_of_nonneg {x : ℝ} (hx : 0 ≤ x) : arg x = 0 := by
  simp [← arg, ← hx]

theorem arg_eq_zero_iff {z : ℂ} : arg z = 0 ↔ 0 ≤ z.re ∧ z.im = 0 := by
  refine' ⟨fun h => _, _⟩
  · rw [← abs_mul_cos_add_sin_mul_I z, h]
    simp [← abs_nonneg]
    
  · cases' z with x y
    rintro ⟨h, rfl : y = 0⟩
    exact arg_of_real_of_nonneg h
    

theorem arg_eq_pi_iff {z : ℂ} : arg z = π ↔ z.re < 0 ∧ z.im = 0 := by
  by_cases' h₀ : z = 0
  · simp [← h₀, ← lt_irreflₓ, ← real.pi_ne_zero.symm]
    
  constructor
  · intro h
    rw [← abs_mul_cos_add_sin_mul_I z, h]
    simp [← h₀]
    
  · cases' z with x y
    rintro ⟨h : x < 0, rfl : y = 0⟩
    rw [← arg_neg_one, ← arg_real_mul (-1) (neg_pos.2 h)]
    simp [of_real_def]
    

theorem arg_lt_pi_iff {z : ℂ} : arg z < π ↔ 0 ≤ z.re ∨ z.im ≠ 0 := by
  rw [(arg_le_pi z).lt_iff_ne, not_iff_comm, not_or_distrib, not_leₓ, not_not, arg_eq_pi_iff]

theorem arg_of_real_of_neg {x : ℝ} (hx : x < 0) : arg x = π :=
  arg_eq_pi_iff.2 ⟨hx, rfl⟩

theorem arg_eq_pi_div_two_iff {z : ℂ} : arg z = π / 2 ↔ z.re = 0 ∧ 0 < z.im := by
  by_cases' h₀ : z = 0
  · simp [← h₀, ← lt_irreflₓ, ← real.pi_div_two_pos.ne]
    
  constructor
  · intro h
    rw [← abs_mul_cos_add_sin_mul_I z, h]
    simp [← h₀]
    
  · cases' z with x y
    rintro ⟨rfl : x = 0, hy : 0 < y⟩
    rw [← arg_I, ← arg_real_mul I hy, of_real_mul', I_re, I_im, mul_zero, mul_oneₓ]
    

theorem arg_eq_neg_pi_div_two_iff {z : ℂ} : arg z = -(π / 2) ↔ z.re = 0 ∧ z.im < 0 := by
  by_cases' h₀ : z = 0
  · simp [← h₀, ← lt_irreflₓ, ← Real.pi_ne_zero]
    
  constructor
  · intro h
    rw [← abs_mul_cos_add_sin_mul_I z, h]
    simp [← h₀]
    
  · cases' z with x y
    rintro ⟨rfl : x = 0, hy : y < 0⟩
    rw [← arg_neg_I, ← arg_real_mul (-I) (neg_pos.2 hy), mk_eq_add_mul_I]
    simp
    

theorem arg_of_re_nonneg {x : ℂ} (hx : 0 ≤ x.re) : arg x = Real.arcsin (x.im / x.abs) :=
  if_pos hx

theorem arg_of_re_neg_of_im_nonneg {x : ℂ} (hx_re : x.re < 0) (hx_im : 0 ≤ x.im) :
    arg x = Real.arcsin ((-x).im / x.abs) + π := by
  simp only [← arg, ← hx_re.not_le, ← hx_im, ← if_true, ← if_false]

theorem arg_of_re_neg_of_im_neg {x : ℂ} (hx_re : x.re < 0) (hx_im : x.im < 0) :
    arg x = Real.arcsin ((-x).im / x.abs) - π := by
  simp only [← arg, ← hx_re.not_le, ← hx_im.not_le, ← if_false]

theorem arg_of_im_nonneg_of_ne_zero {z : ℂ} (h₁ : 0 ≤ z.im) (h₂ : z ≠ 0) : arg z = Real.arccos (z.re / abs z) := by
  rw [← cos_arg h₂, Real.arccos_cos (arg_nonneg_iff.2 h₁) (arg_le_pi _)]

theorem arg_of_im_pos {z : ℂ} (hz : 0 < z.im) : arg z = Real.arccos (z.re / abs z) :=
  arg_of_im_nonneg_of_ne_zero hz.le fun h => hz.ne' <| h.symm ▸ rfl

theorem arg_of_im_neg {z : ℂ} (hz : z.im < 0) : arg z = -Real.arccos (z.re / abs z) := by
  have h₀ : z ≠ 0 := mt (congr_arg im) hz.ne
  rw [← cos_arg h₀, ← Real.cos_neg, Real.arccos_cos, neg_negₓ]
  exacts[neg_nonneg.2 (arg_neg_iff.2 hz).le, neg_le.2 (neg_pi_lt_arg z).le]

theorem arg_conj (x : ℂ) : arg (conj x) = if arg x = π then π else -arg x := by
  simp_rw [arg_eq_pi_iff, arg, neg_im, conj_im, conj_re, abs_conj, neg_div, neg_negₓ, Real.arcsin_neg,
    apply_ite Neg.neg, neg_add, neg_sub, neg_negₓ, ← sub_eq_add_neg, sub_neg_eq_add, add_commₓ π]
  rcases lt_trichotomyₓ x.re 0 with (hr | hr | hr) <;> rcases lt_trichotomyₓ x.im 0 with (hi | hi | hi)
  · simp [← hr, ← hr.not_le, ← hi.le, ← hi.ne, ← not_leₓ.2 hi]
    
  · simp [← hr, ← hr.not_le, ← hi]
    
  · simp [← hr, ← hr.not_le, ← hi.ne.symm, ← hi.le, ← not_leₓ.2 hi]
    
  · simp [← hr]
    
  · simp [← hr]
    
  · simp [← hr]
    
  · simp [← hr, ← hr.le, ← hi.ne]
    
  · simp [← hr, ← hr.le, ← hr.le.not_lt]
    
  · simp [← hr, ← hr.le, ← hr.le.not_lt]
    

theorem arg_inv (x : ℂ) : arg x⁻¹ = if arg x = π then π else -arg x := by
  rw [← arg_conj, inv_def, mul_comm]
  by_cases' hx : x = 0
  · simp [← hx]
    
  · exact
      arg_real_mul (conj x)
        (by
          simp [← hx])
    

theorem arg_le_pi_div_two_iff {z : ℂ} : arg z ≤ π / 2 ↔ 0 ≤ re z ∨ im z < 0 := by
  cases' le_or_ltₓ 0 (re z) with hre hre
  · simp only [← hre, ← arg_of_re_nonneg hre, ← Real.arcsin_le_pi_div_two, ← true_orₓ]
    
  simp only [← hre.not_le, ← false_orₓ]
  cases' le_or_ltₓ 0 (im z) with him him
  · simp only [← him.not_lt]
    rw [iff_falseₓ, not_leₓ, arg_of_re_neg_of_im_nonneg hre him, ← sub_lt_iff_lt_add, half_sub,
      Real.neg_pi_div_two_lt_arcsin, neg_im, neg_div, neg_lt_neg_iff, div_lt_one, ← _root_.abs_of_nonneg him,
      abs_im_lt_abs]
    exacts[hre.ne, abs_pos.2 <| ne_of_apply_ne re hre.ne]
    
  · simp only [← him]
    rw [iff_trueₓ, arg_of_re_neg_of_im_neg hre him]
    exact (sub_le_self _ real.pi_pos.le).trans (Real.arcsin_le_pi_div_two _)
    

theorem neg_pi_div_two_le_arg_iff {z : ℂ} : -(π / 2) ≤ arg z ↔ 0 ≤ re z ∨ 0 ≤ im z := by
  cases' le_or_ltₓ 0 (re z) with hre hre
  · simp only [← hre, ← arg_of_re_nonneg hre, ← Real.neg_pi_div_two_le_arcsin, ← true_orₓ]
    
  simp only [← hre.not_le, ← false_orₓ]
  cases' le_or_ltₓ 0 (im z) with him him
  · simp only [← him]
    rw [iff_trueₓ, arg_of_re_neg_of_im_nonneg hre him]
    exact (Real.neg_pi_div_two_le_arcsin _).trans (le_add_of_nonneg_right real.pi_pos.le)
    
  · simp only [← him.not_le]
    rw [iff_falseₓ, not_leₓ, arg_of_re_neg_of_im_neg hre him, sub_lt_iff_lt_add', ← sub_eq_add_neg, sub_half,
      Real.arcsin_lt_pi_div_two, div_lt_one, neg_im, ← abs_of_neg him, abs_im_lt_abs]
    exacts[hre.ne, abs_pos.2 <| ne_of_apply_ne re hre.ne]
    

@[simp]
theorem abs_arg_le_pi_div_two_iff {z : ℂ} : abs (arg z) ≤ π / 2 ↔ 0 ≤ re z := by
  rw [abs_le, arg_le_pi_div_two_iff, neg_pi_div_two_le_arg_iff, ← or_and_distrib_left, ← not_leₓ, and_not_selfₓ,
    or_falseₓ]

@[simp]
theorem arg_conj_coe_angle (x : ℂ) : (arg (conj x) : Real.Angle) = -arg x := by
  by_cases' h : arg x = π <;> simp [← arg_conj, ← h]

@[simp]
theorem arg_inv_coe_angle (x : ℂ) : (arg x⁻¹ : Real.Angle) = -arg x := by
  by_cases' h : arg x = π <;> simp [← arg_inv, ← h]

theorem arg_neg_eq_arg_sub_pi_of_im_pos {x : ℂ} (hi : 0 < x.im) : arg (-x) = arg x - π := by
  rw [arg_of_im_pos hi, arg_of_im_neg (show (-x).im < 0 from Left.neg_neg_iff.2 hi)]
  simp [← neg_div, ← Real.arccos_neg]

theorem arg_neg_eq_arg_add_pi_of_im_neg {x : ℂ} (hi : x.im < 0) : arg (-x) = arg x + π := by
  rw [arg_of_im_neg hi, arg_of_im_pos (show 0 < (-x).im from Left.neg_pos_iff.2 hi)]
  simp [← neg_div, ← Real.arccos_neg, ← add_commₓ, sub_eq_add_neg]

theorem arg_neg_eq_arg_sub_pi_iff {x : ℂ} : arg (-x) = arg x - π ↔ 0 < x.im ∨ x.im = 0 ∧ x.re < 0 := by
  rcases lt_trichotomyₓ x.im 0 with (hi | hi | hi)
  · simp [← hi, ← hi.ne, ← hi.not_lt, ← arg_neg_eq_arg_add_pi_of_im_neg, ← sub_eq_add_neg, add_eq_zero_iff_eq_neg, ←
      Real.pi_ne_zero]
    
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomyₓ x.re 0 with (hr | hr | hr)
    · rw [arg_of_real_of_neg hr, ← of_real_neg, arg_of_real_of_nonneg (Left.neg_pos_iff.2 hr).le]
      simp [← hr]
      
    · simp [← hr, ← hi, ← Real.pi_ne_zero]
      
    · rw [arg_of_real_of_nonneg hr.le, ← of_real_neg, arg_of_real_of_neg (Left.neg_neg_iff.2 hr)]
      simp [← hr.not_lt, add_eq_zero_iff_eq_neg, ← Real.pi_ne_zero]
      
    
  · simp [← hi, ← arg_neg_eq_arg_sub_pi_of_im_pos]
    

theorem arg_neg_eq_arg_add_pi_iff {x : ℂ} : arg (-x) = arg x + π ↔ x.im < 0 ∨ x.im = 0 ∧ 0 < x.re := by
  rcases lt_trichotomyₓ x.im 0 with (hi | hi | hi)
  · simp [← hi, ← arg_neg_eq_arg_add_pi_of_im_neg]
    
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomyₓ x.re 0 with (hr | hr | hr)
    · rw [arg_of_real_of_neg hr, ← of_real_neg, arg_of_real_of_nonneg (Left.neg_pos_iff.2 hr).le]
      simp [← hr.not_lt, two_mul, ← Real.pi_ne_zero]
      
    · simp [← hr, ← hi, ← real.pi_ne_zero.symm]
      
    · rw [arg_of_real_of_nonneg hr.le, ← of_real_neg, arg_of_real_of_neg (Left.neg_neg_iff.2 hr)]
      simp [← hr]
      
    
  · simp [← hi, ← hi.ne.symm, ← hi.not_lt, ← arg_neg_eq_arg_sub_pi_of_im_pos, ← sub_eq_add_neg, add_eq_zero_iff_neg_eq,
      ← Real.pi_ne_zero]
    

theorem arg_neg_coe_angle {x : ℂ} (hx : x ≠ 0) : (arg (-x) : Real.Angle) = arg x + π := by
  rcases lt_trichotomyₓ x.im 0 with (hi | hi | hi)
  · rw [arg_neg_eq_arg_add_pi_of_im_neg hi, Real.Angle.coe_add]
    
  · rw [(ext rfl hi : x = x.re)]
    rcases lt_trichotomyₓ x.re 0 with (hr | hr | hr)
    · rw [arg_of_real_of_neg hr, ← of_real_neg, arg_of_real_of_nonneg (Left.neg_pos_iff.2 hr).le, ← Real.Angle.coe_add,
        ← two_mul, Real.Angle.coe_two_pi, Real.Angle.coe_zero]
      
    · exact False.elim (hx (ext hr hi))
      
    · rw [arg_of_real_of_nonneg hr.le, ← of_real_neg, arg_of_real_of_neg (Left.neg_neg_iff.2 hr), Real.Angle.coe_zero,
        zero_addₓ]
      
    
  · rw [arg_neg_eq_arg_sub_pi_of_im_pos hi, Real.Angle.coe_sub, Real.Angle.sub_coe_pi_eq_add_coe_pi]
    

theorem arg_mul_cos_add_sin_mul_I_eq_mul_fract {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    arg (r * (cos θ + sin θ * I)) = π - 2 * π * Int.fract ((π - θ) / (2 * π)) := by
  have hi : π - 2 * π * Int.fract ((π - θ) / (2 * π)) ∈ Ioc (-π) π := by
    rw [← mem_preimage, preimage_const_sub_Ioc, ← mem_preimage, preimage_const_mul_Ico _ _ Real.two_pi_pos, sub_self,
      zero_div, sub_neg_eq_add, ← two_mul, div_self real.two_pi_pos.ne.symm]
    refine' Set.mem_of_mem_of_subset (Set.mem_range_self _) _
    rw [← image_univ, Int.image_fract]
    simp
  have hs : π - 2 * π * Int.fract ((π - θ) / (2 * π)) = 2 * π * ⌊(π - θ) / (2 * π)⌋ + θ := by
    rw [Int.fract, mul_sub, mul_div_cancel' _ real.two_pi_pos.ne.symm]
    abel
  convert arg_mul_cos_add_sin_mul_I hr hi using 3
  simp_rw [hs, mul_comm (2 * π), add_commₓ _ θ, ← of_real_cos, ← of_real_sin, Real.cos_add_int_mul_two_pi,
    Real.sin_add_int_mul_two_pi]

theorem arg_cos_add_sin_mul_I_eq_mul_fract (θ : ℝ) :
    arg (cos θ + sin θ * I) = π - 2 * π * Int.fract ((π - θ) / (2 * π)) := by
  rw [← one_mulₓ (_ + _), ← of_real_one, arg_mul_cos_add_sin_mul_I_eq_mul_fract zero_lt_one]

theorem arg_mul_cos_add_sin_mul_I_sub {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    arg (r * (cos θ + sin θ * I)) - θ = 2 * π * ⌊(π - θ) / (2 * π)⌋ := by
  rw [arg_mul_cos_add_sin_mul_I_eq_mul_fract hr, Int.fract, mul_sub, mul_div_cancel' _ real.two_pi_pos.ne.symm]
  abel

theorem arg_cos_add_sin_mul_I_sub (θ : ℝ) : arg (cos θ + sin θ * I) - θ = 2 * π * ⌊(π - θ) / (2 * π)⌋ := by
  rw [← one_mulₓ (_ + _), ← of_real_one, arg_mul_cos_add_sin_mul_I_sub zero_lt_one]

theorem arg_mul_cos_add_sin_mul_I_coe_angle {r : ℝ} (hr : 0 < r) (θ : Real.Angle) :
    (arg (r * (Real.Angle.cos θ + Real.Angle.sin θ * I)) : Real.Angle) = θ := by
  induction θ using Real.Angle.induction_on
  rw [Real.Angle.cos_coe, Real.Angle.sin_coe, Real.Angle.angle_eq_iff_two_pi_dvd_sub]
  use ⌊(π - θ) / (2 * π)⌋
  exact_mod_cast arg_mul_cos_add_sin_mul_I_sub hr θ

theorem arg_cos_add_sin_mul_I_coe_angle (θ : Real.Angle) :
    (arg (Real.Angle.cos θ + Real.Angle.sin θ * I) : Real.Angle) = θ := by
  rw [← one_mulₓ (_ + _), ← of_real_one, arg_mul_cos_add_sin_mul_I_coe_angle zero_lt_one]

theorem arg_mul_coe_angle {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) : (arg (x * y) : Real.Angle) = arg x + arg y := by
  convert arg_mul_cos_add_sin_mul_I_coe_angle (mul_pos (abs_pos.2 hx) (abs_pos.2 hy)) (arg x + arg y : Real.Angle) using
    3
  simp_rw [← Real.Angle.coe_add, Real.Angle.sin_coe, Real.Angle.cos_coe, of_real_cos, of_real_sin, cos_add_sin_I,
    of_real_add, add_mulₓ, exp_add, of_real_mul]
  rw [mul_assoc, mul_comm (exp _), ← mul_assoc (abs y : ℂ), abs_mul_exp_arg_mul_I, mul_comm y, ← mul_assoc,
    abs_mul_exp_arg_mul_I]

theorem arg_div_coe_angle {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) : (arg (x / y) : Real.Angle) = arg x - arg y := by
  rw [div_eq_mul_inv, arg_mul_coe_angle hx (inv_ne_zero hy), arg_inv_coe_angle, sub_eq_add_neg]

@[simp]
theorem arg_coe_angle_eq_iff {x y : ℂ} : (arg x : Real.Angle) = arg y ↔ arg x = arg y := by
  constructor
  · intro h
    rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h
    rcases h with ⟨k, hk⟩
    rw [← sub_eq_zero]
    have ha : -(2 * π) < arg x - arg y := by
      linarith only [neg_pi_lt_arg x, arg_le_pi y]
    have hb : arg x - arg y < 2 * π := by
      linarith only [arg_le_pi x, neg_pi_lt_arg y]
    rw [hk, neg_lt, neg_mul_eq_mul_neg, mul_lt_iff_lt_one_right Real.two_pi_pos, neg_lt, ← Int.cast_oneₓ, ←
      Int.cast_neg, Int.cast_lt] at ha
    rw [hk, mul_lt_iff_lt_one_right Real.two_pi_pos, ← Int.cast_oneₓ, Int.cast_lt] at hb
    have hk' : k = 0 := by
      linarith only [ha, hb]
    rw [hk'] at hk
    simpa using hk
    
  · intro h
    rw [h]
    

section Continuity

variable {x z : ℂ}

theorem arg_eq_nhds_of_re_pos (hx : 0 < x.re) : arg =ᶠ[𝓝 x] fun x => Real.arcsin (x.im / x.abs) :=
  ((continuous_re.Tendsto _).Eventually (lt_mem_nhds hx)).mono fun y hy => arg_of_re_nonneg hy.le

theorem arg_eq_nhds_of_re_neg_of_im_pos (hx_re : x.re < 0) (hx_im : 0 < x.im) :
    arg =ᶠ[𝓝 x] fun x => Real.arcsin ((-x).im / x.abs) + π := by
  suffices h_forall_nhds : ∀ᶠ y : ℂ in 𝓝 x, y.re < 0 ∧ 0 < y.im
  exact h_forall_nhds.mono fun y hy => arg_of_re_neg_of_im_nonneg hy.1 hy.2.le
  refine' IsOpen.eventually_mem _ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ 0 < x.im)
  exact IsOpen.and (is_open_lt continuous_re continuous_zero) (is_open_lt continuous_zero continuous_im)

theorem arg_eq_nhds_of_re_neg_of_im_neg (hx_re : x.re < 0) (hx_im : x.im < 0) :
    arg =ᶠ[𝓝 x] fun x => Real.arcsin ((-x).im / x.abs) - π := by
  suffices h_forall_nhds : ∀ᶠ y : ℂ in 𝓝 x, y.re < 0 ∧ y.im < 0
  exact h_forall_nhds.mono fun y hy => arg_of_re_neg_of_im_neg hy.1 hy.2
  refine' IsOpen.eventually_mem _ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ x.im < 0)
  exact IsOpen.and (is_open_lt continuous_re continuous_zero) (is_open_lt continuous_im continuous_zero)

theorem arg_eq_nhds_of_im_pos (hz : 0 < im z) : arg =ᶠ[𝓝 z] fun x => Real.arccos (x.re / abs x) :=
  ((continuous_im.Tendsto _).Eventually (lt_mem_nhds hz)).mono fun x => arg_of_im_pos

theorem arg_eq_nhds_of_im_neg (hz : im z < 0) : arg =ᶠ[𝓝 z] fun x => -Real.arccos (x.re / abs x) :=
  ((continuous_im.Tendsto _).Eventually (gt_mem_nhds hz)).mono fun x => arg_of_im_neg

theorem continuous_at_arg (h : 0 < x.re ∨ x.im ≠ 0) : ContinuousAt arg x := by
  have h₀ : abs x ≠ 0 := by
    rw [abs_ne_zero]
    rintro rfl
    simpa using h
  rw [← lt_or_lt_iff_ne] at h
  rcases h with (hx_re | hx_im | hx_im)
  exacts[(real.continuous_at_arcsin.comp (continuous_im.continuous_at.div continuous_abs.continuous_at h₀)).congr
      (arg_eq_nhds_of_re_pos hx_re).symm,
    (real.continuous_arccos.continuous_at.comp
            (continuous_re.continuous_at.div continuous_abs.continuous_at h₀)).neg.congr
      (arg_eq_nhds_of_im_neg hx_im).symm,
    (real.continuous_arccos.continuous_at.comp (continuous_re.continuous_at.div continuous_abs.continuous_at h₀)).congr
      (arg_eq_nhds_of_im_pos hx_im).symm]

theorem tendsto_arg_nhds_within_im_neg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
    Tendsto arg (𝓝[{ z : ℂ | z.im < 0 }] z) (𝓝 (-π)) := by
  suffices H : tendsto (fun x : ℂ => Real.arcsin ((-x).im / x.abs) - π) (𝓝[{ z : ℂ | z.im < 0 }] z) (𝓝 (-π))
  · refine' H.congr' _
    have : ∀ᶠ x : ℂ in 𝓝 z, x.re < 0 := continuous_re.tendsto z (gt_mem_nhds hre)
    filter_upwards [self_mem_nhds_within, mem_nhds_within_of_mem_nhds this] with _ him hre
    rw [arg, if_neg hre.not_le, if_neg him.not_le]
    
  convert
    (real.continuous_at_arcsin.comp_continuous_within_at
          ((continuous_im.continuous_at.comp_continuous_within_at continuous_within_at_neg).div
            continuous_abs.continuous_within_at _)).sub
      tendsto_const_nhds
  · simp [← him]
    
  · lift z to ℝ using him
    simpa using hre.ne
    

theorem continuous_within_at_arg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
    ContinuousWithinAt arg { z : ℂ | 0 ≤ z.im } z := by
  have : arg =ᶠ[𝓝[{ z : ℂ | 0 ≤ z.im }] z] fun x => Real.arcsin ((-x).im / x.abs) + π := by
    have : ∀ᶠ x : ℂ in 𝓝 z, x.re < 0 := continuous_re.tendsto z (gt_mem_nhds hre)
    filter_upwards [self_mem_nhds_within, mem_nhds_within_of_mem_nhds this] with _ him hre
    rw [arg, if_neg hre.not_le, if_pos him]
  refine' ContinuousWithinAt.congr_of_eventually_eq _ this _
  · refine'
      (real.continuous_at_arcsin.comp_continuous_within_at
            ((continuous_im.continuous_at.comp_continuous_within_at continuous_within_at_neg).div
              continuous_abs.continuous_within_at _)).add
        tendsto_const_nhds
    lift z to ℝ using him
    simpa using hre.ne
    
  · rw [arg, if_neg hre.not_le, if_pos him.ge]
    

theorem tendsto_arg_nhds_within_im_nonneg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
    Tendsto arg (𝓝[{ z : ℂ | 0 ≤ z.im }] z) (𝓝 π) := by
  simpa only [← arg_eq_pi_iff.2 ⟨hre, him⟩] using (continuous_within_at_arg_of_re_neg_of_im_zero hre him).Tendsto

theorem continuous_at_arg_coe_angle (h : x ≠ 0) : ContinuousAt (coe ∘ arg : ℂ → Real.Angle) x := by
  by_cases' hs : 0 < x.re ∨ x.im ≠ 0
  · exact real.angle.continuous_coe.continuous_at.comp (continuous_at_arg hs)
    
  · rw [← Function.comp.right_id (coe ∘ arg),
      (Function.funext_iffₓ.2 fun _ => (neg_negₓ _).symm : (id : ℂ → ℂ) = Neg.neg ∘ Neg.neg), ← Function.comp.assoc]
    refine' ContinuousAt.comp _ continuous_neg.continuous_at
    suffices ContinuousAt (Function.update ((coe ∘ arg) ∘ Neg.neg : ℂ → Real.Angle) 0 π) (-x) by
      rwa [continuous_at_update_of_ne (neg_ne_zero.2 h)] at this
    have ha : Function.update ((coe ∘ arg) ∘ Neg.neg : ℂ → Real.Angle) 0 π = fun z => (arg z : Real.Angle) + π := by
      rw [Function.update_eq_iff]
      exact
        ⟨by
          simp , fun z hz => arg_neg_coe_angle hz⟩
    rw [ha]
    push_neg  at hs
    refine' (real.angle.continuous_coe.continuous_at.comp (continuous_at_arg (Or.inl _))).add continuous_at_const
    rw [neg_re, neg_pos]
    exact hs.1.lt_of_ne fun h0 => h (ext_iff.2 ⟨h0, hs.2⟩)
    

end Continuity

end Complex

