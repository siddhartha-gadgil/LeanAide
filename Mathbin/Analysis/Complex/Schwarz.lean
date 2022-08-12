/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Analysis.Complex.AbsMax
import Mathbin.Analysis.Complex.RemovableSingularity

/-!
# Schwarz lemma

In this file we prove several versions of the Schwarz lemma.

* `complex.norm_deriv_le_div_of_maps_to_ball`, `complex.abs_deriv_le_div_of_maps_to_ball`: if
  `f : ℂ → E` sends an open disk with center `c` and a positive radius `R₁` to an open ball with
  center `f c` and radius `R₂`, then the absolute value of the derivative of `f` at `c` is at most
  the ratio `R₂ / R₁`;

* `complex.dist_le_div_mul_dist_of_maps_to_ball`: if `f : ℂ → E` sends an open disk with center `c`
  and radius `R₁` to an open disk with center `f c` and radius `R₂`, then for any `z` in the former
  disk we have `dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`;

* `complex.abs_deriv_le_one_of_maps_to_ball`: if `f : ℂ → ℂ` sends an open disk of positive radius
  to itself and the center of this disk to itself, then the absolute value of the derivative of `f`
  at the center of this disk is at most `1`;

* `complex.dist_le_dist_of_maps_to_ball`: if `f : ℂ → ℂ` sends an open disk to itself and the center
  `c` of this disk to itself, then for any point `z` of this disk we have `dist (f z) c ≤ dist z c`;

* `complex.abs_le_abs_of_maps_to_ball`: if `f : ℂ → ℂ` sends an open disk with center `0` to itself,
  then for any point `z` of this disk we have `abs (f z) ≤ abs z`.

## Implementation notes

We prove some versions of the Schwarz lemma for a map `f : ℂ → E` taking values in any normed space
over complex numbers.

## TODO

* Prove that these inequalities are strict unless `f` is an affine map.

* Prove that any diffeomorphism of the unit disk to itself is a Möbius map.

## Tags

Schwarz lemma
-/


open Metric Set Function Filter TopologicalSpace

open TopologicalSpace

namespace Complex

section Space

variable {E : Type _} [NormedGroup E] [NormedSpace ℂ E] {R R₁ R₂ : ℝ} {f : ℂ → E} {c z : ℂ}

/-- An auxiliary lemma for `complex.norm_dslope_le_div_of_maps_to_ball`. -/
theorem schwarz_aux {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (Ball c R₁)) (h_maps : MapsTo f (Ball c R₁) (Ball (f c) R₂))
    (hz : z ∈ Ball c R₁) : ∥dslope f c z∥ ≤ R₂ / R₁ := by
  have hR₁ : 0 < R₁ := nonempty_ball.1 ⟨z, hz⟩
  suffices ∀ᶠ r in 𝓝[<] R₁, ∥dslope f c z∥ ≤ R₂ / r by
    refine' ge_of_tendsto _ this
    exact (tendsto_const_nhds.div tendsto_id hR₁.ne').mono_left nhds_within_le_nhds
  rw [mem_ball] at hz
  filter_upwards [Ioo_mem_nhds_within_Iio ⟨hz, le_rfl⟩] with r hr
  have hr₀ : 0 < r := dist_nonneg.trans_lt hr.1
  replace hd : DiffContOnCl ℂ (dslope f c) (ball c r)
  · refine' DifferentiableOn.diff_cont_on_cl _
    rw [closure_ball c hr₀.ne']
    exact ((differentiable_on_dslope <| ball_mem_nhds _ hR₁).mpr hd).mono (closed_ball_subset_ball hr.2)
    
  refine' norm_le_of_forall_mem_frontier_norm_le bounded_ball hd _ _
  · rw [frontier_ball c hr₀.ne']
    intro z hz
    have hz' : z ≠ c := ne_of_mem_sphere hz hr₀.ne'
    rw [dslope_of_ne _ hz', slope_def_module, norm_smul, norm_inv, (mem_sphere_iff_norm _ _ _).1 hz, ← div_eq_inv_mul,
      div_le_div_right hr₀, ← dist_eq_norm]
    exact
      le_of_ltₓ
        (h_maps
          (mem_ball.2
            (by
              rw [mem_sphere.1 hz]
              exact hr.2)))
    
  · rw [closure_ball c hr₀.ne', mem_closed_ball]
    exact hr.1.le
    

/-- Two cases of the **Schwarz Lemma** (derivative and distance), merged together. -/
theorem norm_dslope_le_div_of_maps_to_ball (hd : DifferentiableOn ℂ f (Ball c R₁))
    (h_maps : MapsTo f (Ball c R₁) (Ball (f c) R₂)) (hz : z ∈ Ball c R₁) : ∥dslope f c z∥ ≤ R₂ / R₁ := by
  have hR₁ : 0 < R₁ := nonempty_ball.1 ⟨z, hz⟩
  have hR₂ : 0 < R₂ := nonempty_ball.1 ⟨f z, h_maps hz⟩
  cases' eq_or_ne (dslope f c z) 0 with hc hc
  · rw [hc, norm_zero]
    exact div_nonneg hR₂.le hR₁.le
    
  rcases exists_dual_vector ℂ _ hc with ⟨g, hg, hgf⟩
  have hg' : ∥g∥₊ = 1 := Nnreal.eq hg
  have hg₀ : ∥g∥₊ ≠ 0 := by
    simpa only [← hg'] using one_ne_zero
  calc ∥dslope f c z∥ = ∥dslope (g ∘ f) c z∥ := by
      rw [g.dslope_comp, hgf, IsROrC.norm_of_real, norm_norm]
      exact fun _ => hd.differentiable_at (ball_mem_nhds _ hR₁)_ ≤ R₂ / R₁ := by
      refine' schwarz_aux (g.differentiable.comp_differentiable_on hd) (maps_to.comp _ h_maps) hz
      simpa only [← hg', ← Nnreal.coe_one, ← one_mulₓ] using g.lipschitz.maps_to_ball hg₀ (f c) R₂

/-- The **Schwarz Lemma**: if `f : ℂ → E` sends an open disk with center `c` and a positive radius
`R₁` to an open ball with center `f c` and radius `R₂`, then the absolute value of the derivative of
`f` at `c` is at most the ratio `R₂ / R₁`. -/
theorem norm_deriv_le_div_of_maps_to_ball (hd : DifferentiableOn ℂ f (Ball c R₁))
    (h_maps : MapsTo f (Ball c R₁) (Ball (f c) R₂)) (h₀ : 0 < R₁) : ∥deriv f c∥ ≤ R₂ / R₁ := by
  simpa only [← dslope_same] using norm_dslope_le_div_of_maps_to_ball hd h_maps (mem_ball_self h₀)

/-- The **Schwarz Lemma**: if `f : ℂ → E` sends an open disk with center `c` and radius `R₁` to an
open ball with center `f c` and radius `R₂`, then for any `z` in the former disk we have
`dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`. -/
theorem dist_le_div_mul_dist_of_maps_to_ball (hd : DifferentiableOn ℂ f (Ball c R₁))
    (h_maps : MapsTo f (Ball c R₁) (Ball (f c) R₂)) (hz : z ∈ Ball c R₁) : dist (f z) (f c) ≤ R₂ / R₁ * dist z c := by
  rcases eq_or_ne z c with (rfl | hne)
  · simp only [← dist_self, ← mul_zero]
    
  simpa only [← dslope_of_ne _ hne, ← slope_def_module, ← norm_smul, ← norm_inv, div_eq_inv_mul, dist_eq_norm, ←
    div_le_iff (dist_pos.2 hne)] using norm_dslope_le_div_of_maps_to_ball hd h_maps hz

end Space

variable {f : ℂ → ℂ} {c z : ℂ} {R R₁ R₂ : ℝ}

/-- The **Schwarz Lemma**: if `f : ℂ → ℂ` sends an open disk with center `c` and a positive radius
`R₁` to an open disk with center `f c` and radius `R₂`, then the absolute value of the derivative of
`f` at `c` is at most the ratio `R₂ / R₁`. -/
theorem abs_deriv_le_div_of_maps_to_ball (hd : DifferentiableOn ℂ f (Ball c R₁))
    (h_maps : MapsTo f (Ball c R₁) (Ball (f c) R₂)) (h₀ : 0 < R₁) : abs (deriv f c) ≤ R₂ / R₁ :=
  norm_deriv_le_div_of_maps_to_ball hd h_maps h₀

/-- The **Schwarz Lemma**: if `f : ℂ → ℂ` sends an open disk of positive radius to itself and the
center of this disk to itself, then the absolute value of the derivative of `f` at the center of
this disk is at most `1`. -/
theorem abs_deriv_le_one_of_maps_to_ball (hd : DifferentiableOn ℂ f (Ball c R))
    (h_maps : MapsTo f (Ball c R) (Ball c R)) (hc : f c = c) (h₀ : 0 < R) : abs (deriv f c) ≤ 1 :=
  (norm_deriv_le_div_of_maps_to_ball hd
        (by
          rwa [hc])
        h₀).trans_eq
    (div_self h₀.ne')

/-- The **Schwarz Lemma**: if `f : ℂ → ℂ` sends an open disk to itself and the center `c` of this
disk to itself, then for any point `z` of this disk we have `dist (f z) c ≤ dist z c`. -/
theorem dist_le_dist_of_maps_to_ball_self (hd : DifferentiableOn ℂ f (Ball c R))
    (h_maps : MapsTo f (Ball c R) (Ball c R)) (hc : f c = c) (hz : z ∈ Ball c R) : dist (f z) c ≤ dist z c := by
  have hR : 0 < R := nonempty_ball.1 ⟨z, hz⟩
  simpa only [← hc, ← div_self hR.ne', ← one_mulₓ] using
    dist_le_div_mul_dist_of_maps_to_ball hd
      (by
        rwa [hc])
      hz

/-- The **Schwarz Lemma**: if `f : ℂ → ℂ` sends an open disk with center `0` to itself, the for any
point `z` of this disk we have `abs (f z) ≤ abs z`. -/
theorem abs_le_abs_of_maps_to_ball_self (hd : DifferentiableOn ℂ f (Ball 0 R)) (h_maps : MapsTo f (Ball 0 R) (Ball 0 R))
    (h₀ : f 0 = 0) (hz : abs z < R) : abs (f z) ≤ abs z := by
  replace hz : z ∈ ball (0 : ℂ) R
  exact mem_ball_zero_iff.2 hz
  simpa only [← dist_zero_right] using dist_le_dist_of_maps_to_ball_self hd h_maps h₀ hz

end Complex

