/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import Mathbin.Analysis.Complex.Basic
import Mathbin.Data.Complex.Exponential

/-!
# Complex and real exponential

In this file we prove continuity of `complex.exp` and `real.exp`. We also prove a few facts about
limits of `real.exp` at infinity.

## Tags

exp
-/


noncomputable section

open Finset Filter Metric Asymptotics Set Function

open Classical TopologicalSpace

namespace Complex

variable {z y x : ℝ}

theorem exp_bound_sq (x z : ℂ) (hz : ∥z∥ ≤ 1) : ∥exp (x + z) - exp x - z • exp x∥ ≤ ∥exp x∥ * ∥z∥ ^ 2 :=
  calc
    ∥exp (x + z) - exp x - z * exp x∥ = ∥exp x * (exp z - 1 - z)∥ := by
      congr
      rw [exp_add]
      ring
    _ = ∥exp x∥ * ∥exp z - 1 - z∥ := norm_mul _ _
    _ ≤ ∥exp x∥ * ∥z∥ ^ 2 := mul_le_mul_of_nonneg_left (abs_exp_sub_one_sub_id_le hz) (norm_nonneg _)
    

theorem locally_lipschitz_exp {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_le : r ≤ 1) (x y : ℂ) (hyx : ∥y - x∥ < r) :
    ∥exp y - exp x∥ ≤ (1 + r) * ∥exp x∥ * ∥y - x∥ := by
  have hy_eq : y = x + (y - x) := by
    abel
  have hyx_sq_le : ∥y - x∥ ^ 2 ≤ r * ∥y - x∥ := by
    rw [pow_two]
    exact mul_le_mul hyx.le le_rfl (norm_nonneg _) hr_nonneg
  have h_sq : ∀ z, ∥z∥ ≤ 1 → ∥exp (x + z) - exp x∥ ≤ ∥z∥ * ∥exp x∥ + ∥exp x∥ * ∥z∥ ^ 2 := by
    intro z hz
    have : ∥exp (x + z) - exp x - z • exp x∥ ≤ ∥exp x∥ * ∥z∥ ^ 2 := exp_bound_sq x z hz
    rw [← sub_le_iff_le_add', ← norm_smul z]
    exact (norm_sub_norm_le _ _).trans this
  calc ∥exp y - exp x∥ = ∥exp (x + (y - x)) - exp x∥ := by
      nth_rw 0[hy_eq]_ ≤ ∥y - x∥ * ∥exp x∥ + ∥exp x∥ * ∥y - x∥ ^ 2 :=
      h_sq (y - x) (hyx.le.trans hr_le)_ ≤ ∥y - x∥ * ∥exp x∥ + ∥exp x∥ * (r * ∥y - x∥) :=
      add_le_add_left (mul_le_mul le_rfl hyx_sq_le (sq_nonneg _) (norm_nonneg _)) _ _ = (1 + r) * ∥exp x∥ * ∥y - x∥ :=
      by
      ring

@[continuity]
theorem continuous_exp : Continuous exp :=
  continuous_iff_continuous_at.mpr fun x =>
    continuous_at_of_locally_lipschitz zero_lt_one (2 * ∥exp x∥) (locally_lipschitz_exp zero_le_one le_rfl x)

theorem continuous_on_exp {s : Set ℂ} : ContinuousOn exp s :=
  continuous_exp.ContinuousOn

end Complex

section ComplexContinuousExpComp

variable {α : Type _}

open Complex

theorem Filter.Tendsto.cexp {l : Filter α} {f : α → ℂ} {z : ℂ} (hf : Tendsto f l (𝓝 z)) :
    Tendsto (fun x => exp (f x)) l (𝓝 (exp z)) :=
  (continuous_exp.Tendsto _).comp hf

variable [TopologicalSpace α] {f : α → ℂ} {s : Set α} {x : α}

theorem ContinuousWithinAt.cexp (h : ContinuousWithinAt f s x) : ContinuousWithinAt (fun y => exp (f y)) s x :=
  h.cexp

theorem ContinuousAt.cexp (h : ContinuousAt f x) : ContinuousAt (fun y => exp (f y)) x :=
  h.cexp

theorem ContinuousOn.cexp (h : ContinuousOn f s) : ContinuousOn (fun y => exp (f y)) s := fun x hx => (h x hx).cexp

theorem Continuous.cexp (h : Continuous f) : Continuous fun y => exp (f y) :=
  continuous_iff_continuous_at.2 fun x => h.ContinuousAt.cexp

end ComplexContinuousExpComp

namespace Real

@[continuity]
theorem continuous_exp : Continuous exp :=
  Complex.continuous_re.comp Complex.continuous_of_real.cexp

theorem continuous_on_exp {s : Set ℝ} : ContinuousOn exp s :=
  continuous_exp.ContinuousOn

end Real

section RealContinuousExpComp

variable {α : Type _}

open Real

theorem Filter.Tendsto.exp {l : Filter α} {f : α → ℝ} {z : ℝ} (hf : Tendsto f l (𝓝 z)) :
    Tendsto (fun x => exp (f x)) l (𝓝 (exp z)) :=
  (continuous_exp.Tendsto _).comp hf

variable [TopologicalSpace α] {f : α → ℝ} {s : Set α} {x : α}

theorem ContinuousWithinAt.exp (h : ContinuousWithinAt f s x) : ContinuousWithinAt (fun y => exp (f y)) s x :=
  h.exp

theorem ContinuousAt.exp (h : ContinuousAt f x) : ContinuousAt (fun y => exp (f y)) x :=
  h.exp

theorem ContinuousOn.exp (h : ContinuousOn f s) : ContinuousOn (fun y => exp (f y)) s := fun x hx => (h x hx).exp

theorem Continuous.exp (h : Continuous f) : Continuous fun y => exp (f y) :=
  continuous_iff_continuous_at.2 fun x => h.ContinuousAt.exp

end RealContinuousExpComp

namespace Real

variable {x y z : ℝ}

theorem exp_half (x : ℝ) : exp (x / 2) = sqrt (exp x) := by
  rw [eq_comm, sqrt_eq_iff_sq_eq, sq, ← exp_add, add_halves] <;> exact (exp_pos _).le

/-- The real exponential function tends to `+∞` at `+∞`. -/
theorem tendsto_exp_at_top : Tendsto exp atTop atTop := by
  have A : tendsto (fun x : ℝ => x + 1) at_top at_top := tendsto_at_top_add_const_right at_top 1 tendsto_id
  have B : ∀ᶠ x in at_top, x + 1 ≤ exp x := eventually_at_top.2 ⟨0, fun x hx => add_one_le_exp x⟩
  exact tendsto_at_top_mono' at_top B A

/-- The real exponential function tends to `0` at `-∞` or, equivalently, `exp(-x)` tends to `0`
at `+∞` -/
theorem tendsto_exp_neg_at_top_nhds_0 : Tendsto (fun x => exp (-x)) atTop (𝓝 0) :=
  (tendsto_inv_at_top_zero.comp tendsto_exp_at_top).congr fun x => (exp_neg x).symm

/-- The real exponential function tends to `1` at `0`. -/
theorem tendsto_exp_nhds_0_nhds_1 : Tendsto exp (𝓝 0) (𝓝 1) := by
  convert continuous_exp.tendsto 0
  simp

theorem tendsto_exp_at_bot : Tendsto exp atBot (𝓝 0) :=
  (tendsto_exp_neg_at_top_nhds_0.comp tendsto_neg_at_bot_at_top).congr fun x => congr_arg exp <| neg_negₓ x

theorem tendsto_exp_at_bot_nhds_within : Tendsto exp atBot (𝓝[>] 0) :=
  tendsto_inf.2 ⟨tendsto_exp_at_bot, tendsto_principal.2 <| eventually_of_forall exp_pos⟩

@[simp]
theorem is_bounded_under_ge_exp_comp {α : Type _} (l : Filter α) (f : α → ℝ) :
    IsBoundedUnder (· ≥ ·) l fun x => exp (f x) :=
  is_bounded_under_of ⟨0, fun x => (exp_pos _).le⟩

@[simp]
theorem is_bounded_under_le_exp_comp {α : Type _} {l : Filter α} {f : α → ℝ} :
    (IsBoundedUnder (· ≤ ·) l fun x => exp (f x)) ↔ IsBoundedUnder (· ≤ ·) l f :=
  exp_monotone.is_bounded_under_le_comp tendsto_exp_at_top

/-- The function `exp(x)/x^n` tends to `+∞` at `+∞`, for any natural number `n` -/
theorem tendsto_exp_div_pow_at_top (n : ℕ) : Tendsto (fun x => exp x / x ^ n) atTop atTop := by
  refine' (at_top_basis_Ioi.tendsto_iff (at_top_basis' 1)).2 fun C hC₁ => _
  have hC₀ : 0 < C := zero_lt_one.trans_le hC₁
  have : 0 < (exp 1 * C)⁻¹ := inv_pos.2 (mul_pos (exp_pos _) hC₀)
  obtain ⟨N, hN⟩ : ∃ N, ∀, ∀ k ≥ N, ∀, (↑k ^ n : ℝ) / exp 1 ^ k < (exp 1 * C)⁻¹ :=
    eventually_at_top.1
      ((tendsto_pow_const_div_const_pow_of_one_lt n (one_lt_exp_iff.2 zero_lt_one)).Eventually (gt_mem_nhds this))
  simp only [exp_nat_mul, ← mul_oneₓ, ← div_lt_iff, ← exp_pos, div_eq_inv_mul] at hN
  refine' ⟨N, trivialₓ, fun x hx => _⟩
  rw [Set.mem_Ioi] at hx
  have hx₀ : 0 < x := N.cast_nonneg.trans_lt hx
  rw [Set.mem_Ici, le_div_iff (pow_pos hx₀ _), ← le_div_iff' hC₀]
  calc x ^ n ≤ ⌈x⌉₊ ^ n := pow_le_pow_of_le_left hx₀.le (Nat.le_ceil _) _ _ ≤ exp ⌈x⌉₊ / (exp 1 * C) :=
      (hN _ (Nat.lt_ceil.2 hx).le).le _ ≤ exp (x + 1) / (exp 1 * C) :=
      div_le_div_of_le (mul_pos (exp_pos _) hC₀).le (exp_le_exp.2 <| (Nat.ceil_lt_add_one hx₀.le).le)_ = exp x / C := by
      rw [add_commₓ, exp_add, mul_div_mul_left _ _ (exp_pos _).ne']

/-- The function `x^n * exp(-x)` tends to `0` at `+∞`, for any natural number `n`. -/
theorem tendsto_pow_mul_exp_neg_at_top_nhds_0 (n : ℕ) : Tendsto (fun x => x ^ n * exp (-x)) atTop (𝓝 0) :=
  (tendsto_inv_at_top_zero.comp (tendsto_exp_div_pow_at_top n)).congr fun x => by
    rw [comp_app, inv_eq_one_div, div_div_eq_mul_div, one_mulₓ, div_eq_mul_inv, exp_neg]

/-- The function `(b * exp x + c) / (x ^ n)` tends to `+∞` at `+∞`, for any natural number
`n` and any real numbers `b` and `c` such that `b` is positive. -/
theorem tendsto_mul_exp_add_div_pow_at_top (b c : ℝ) (n : ℕ) (hb : 0 < b) :
    Tendsto (fun x => (b * exp x + c) / x ^ n) atTop atTop := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp only [← pow_zeroₓ, ← div_one]
    exact (tendsto_exp_at_top.const_mul_at_top hb).at_top_add tendsto_const_nhds
    
  simp only [← add_div, ← mul_div_assoc]
  exact
    ((tendsto_exp_div_pow_at_top n).const_mul_at_top hb).at_top_add
      (tendsto_const_nhds.div_at_top (tendsto_pow_at_top hn))

/-- The function `(x ^ n) / (b * exp x + c)` tends to `0` at `+∞`, for any natural number
`n` and any real numbers `b` and `c` such that `b` is nonzero. -/
theorem tendsto_div_pow_mul_exp_add_at_top (b c : ℝ) (n : ℕ) (hb : 0 ≠ b) :
    Tendsto (fun x => x ^ n / (b * exp x + c)) atTop (𝓝 0) := by
  have H : ∀ d e, 0 < d → tendsto (fun x : ℝ => x ^ n / (d * exp x + e)) at_top (𝓝 0) := by
    intro b' c' h
    convert (tendsto_mul_exp_add_div_pow_at_top b' c' n h).inv_tendsto_at_top
    ext x
    simpa only [← Pi.inv_apply] using (inv_div _ _).symm
  cases lt_or_gt_of_neₓ hb
  · exact H b c h
    
  · convert (H (-b) (-c) (neg_pos.mpr h)).neg
    · ext x
      field_simp
      rw [← neg_add (b * exp x) c, neg_div_neg_eq]
      
    · exact neg_zero.symm
      
    

/-- `real.exp` as an order isomorphism between `ℝ` and `(0, +∞)`. -/
def expOrderIso : ℝ ≃o Ioi (0 : ℝ) :=
  StrictMono.orderIsoOfSurjective _ (exp_strict_mono.codRestrict exp_pos) <|
    (continuous_subtype_mk _ continuous_exp).Surjective
      (by
        simp only [← tendsto_Ioi_at_top, ← Subtype.coe_mk, ← tendsto_exp_at_top])
      (by
        simp [← tendsto_exp_at_bot_nhds_within])

@[simp]
theorem coe_exp_order_iso_apply (x : ℝ) : (expOrderIso x : ℝ) = exp x :=
  rfl

@[simp]
theorem coe_comp_exp_order_iso : coe ∘ exp_order_iso = exp :=
  rfl

@[simp]
theorem range_exp : Range exp = Ioi 0 := by
  rw [← coe_comp_exp_order_iso, range_comp, exp_order_iso.range_eq, image_univ, Subtype.range_coe]

@[simp]
theorem map_exp_at_top : map exp atTop = at_top := by
  rw [← coe_comp_exp_order_iso, ← Filter.map_map, OrderIso.map_at_top, map_coe_Ioi_at_top]

@[simp]
theorem comap_exp_at_top : comap exp atTop = at_top := by
  rw [← map_exp_at_top, comap_map exp_injective, map_exp_at_top]

@[simp]
theorem tendsto_exp_comp_at_top {α : Type _} {l : Filter α} {f : α → ℝ} :
    Tendsto (fun x => exp (f x)) l atTop ↔ Tendsto f l atTop := by
  rw [← tendsto_comap_iff, comap_exp_at_top]

theorem tendsto_comp_exp_at_top {α : Type _} {l : Filter α} {f : ℝ → α} :
    Tendsto (fun x => f (exp x)) atTop l ↔ Tendsto f atTop l := by
  rw [← tendsto_map'_iff, map_exp_at_top]

@[simp]
theorem map_exp_at_bot : map exp atBot = 𝓝[>] 0 := by
  rw [← coe_comp_exp_order_iso, ← Filter.map_map, exp_order_iso.map_at_bot, ← map_coe_Ioi_at_bot]

@[simp]
theorem comap_exp_nhds_within_Ioi_zero : comap exp (𝓝[>] 0) = at_bot := by
  rw [← map_exp_at_bot, comap_map exp_injective]

theorem tendsto_comp_exp_at_bot {α : Type _} {l : Filter α} {f : ℝ → α} :
    Tendsto (fun x => f (exp x)) atBot l ↔ Tendsto f (𝓝[>] 0) l := by
  rw [← map_exp_at_bot, tendsto_map'_iff]

@[simp]
theorem comap_exp_nhds_zero : comap exp (𝓝 0) = at_bot :=
  (comap_nhds_within_range exp 0).symm.trans <| by
    simp

theorem is_o_pow_exp_at_top {n : ℕ} : (fun x => x ^ n) =o[at_top] Real.exp := by
  simpa [← is_o_iff_tendsto fun x hx => ((exp_pos x).ne' hx).elim] using
    tendsto_div_pow_mul_exp_add_at_top 1 0 n zero_ne_one

/-- `real.exp (f x)` is bounded away from zero along a filter if and only if this filter is bounded
from below under `f`. -/
@[simp]
theorem is_O_one_exp_comp {α : Type _} {l : Filter α} {f : α → ℝ} :
    ((fun x => 1 : α → ℝ) =O[l] fun x => exp (f x)) ↔ IsBoundedUnder (· ≥ ·) l f :=
  calc
    ((fun x => 1 : α → ℝ) =O[l] fun x => exp (f x)) ↔ ∃ b : ℝ, 0 < b ∧ ∀ᶠ x in l, b ≤ exp (f x) :=
      Iff.trans (is_O_const_left_iff_pos_le_norm one_ne_zero) <| by
        simp only [← norm_eq_abs, ← abs_exp]
    _ ↔ IsBoundedUnder (· ≥ ·) l fun x => expOrderIso (f x) := by
      simp only [← is_bounded_under, ← is_bounded, ← eventually_map, ← SetCoe.exists, ← ge_iff_le, Subtype.coe_le_coe, ←
        exists_prop, ← coe_exp_order_iso_apply, ← Subtype.coe_mk, ← Set.mem_Ioi]
    _ ↔ IsBoundedUnder (· ≥ ·) l f := expOrderIso.Monotone.is_bounded_under_ge_comp expOrderIso.tendsto_at_bot
    

end Real

namespace Complex

theorem comap_exp_comap_abs_at_top : comap exp (comap abs atTop) = comap re atTop :=
  calc
    comap exp (comap abs atTop) = comap re (comap Real.exp atTop) := by
      simp only [← comap_comap, ← (· ∘ ·), ← abs_exp]
    _ = comap re atTop := by
      rw [Real.comap_exp_at_top]
    

theorem comap_exp_nhds_zero : comap exp (𝓝 0) = comap re atBot :=
  calc
    comap exp (𝓝 0) = comap re (comap Real.exp (𝓝 0)) := by
      simp only [← comap_comap, comap_abs_nhds_zero, ← (· ∘ ·), ← abs_exp]
    _ = comap re atBot := by
      rw [Real.comap_exp_nhds_zero]
    

theorem comap_exp_nhds_within_zero : comap exp (𝓝[≠] 0) = comap re atBot := by
  have : exp ⁻¹' {0}ᶜ = univ := eq_univ_of_forall exp_ne_zero
  simp [← nhdsWithin, ← comap_exp_nhds_zero, ← this]

theorem tendsto_exp_nhds_zero_iff {α : Type _} {l : Filter α} {f : α → ℂ} :
    Tendsto (fun x => exp (f x)) l (𝓝 0) ↔ Tendsto (fun x => re (f x)) l atBot := by
  rw [← tendsto_comap_iff, comap_exp_nhds_zero, tendsto_comap_iff]

/-- `complex.abs (complex.exp z) → ∞` as `complex.re z → ∞`. TODO: use `bornology.cobounded`. -/
theorem tendsto_exp_comap_re_at_top : Tendsto exp (comap re atTop) (comap abs atTop) :=
  comap_exp_comap_abs_at_top ▸ tendsto_comap

/-- `complex.exp z → 0` as `complex.re z → -∞`.-/
theorem tendsto_exp_comap_re_at_bot : Tendsto exp (comap re atBot) (𝓝 0) :=
  comap_exp_nhds_zero ▸ tendsto_comap

theorem tendsto_exp_comap_re_at_bot_nhds_within : Tendsto exp (comap re atBot) (𝓝[≠] 0) :=
  comap_exp_nhds_within_zero ▸ tendsto_comap

end Complex

