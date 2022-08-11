/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathbin.Analysis.InnerProductSpace.PiL2
import Mathbin.Combinatorics.Additive.SalemSpencer

/-!
# Behrend's bound on Roth numbers

This file proves Behrend's lower bound on Roth numbers. This says that we can find a subset of
`{1, ..., n}` of size `n / exp (O (sqrt (log n)))` which does not contain arithmetic progressions of
length `3`.

The idea is that the sphere (in the `n` dimensional Euclidean space) doesn't contain arithmetic
progressions (literally) because the corresponding ball is strictly convex. Thus we can take
integer points on that sphere and map them onto `ℕ` in a way that preserves arithmetic progressions
(`behrend.map`).

## Main declarations

* `behrend.sphere`: The intersection of the Euclidean sphere with the positive integer quadrant.
  This is the set that we will map on `ℕ`.
* `behrend.map`: Given a natural number `d`, `behrend.map d : ℕⁿ → ℕ` reads off the coordinates as
  digits in base `d`.
* `behrend.card_sphere_le_roth_number_nat`: Implicit lower bound on Roth numbers in terms of
  `behrend.sphere`.

## References

* [Bryan Gillespie, *Behrend’s Construction*]
  (http://www.epsilonsmall.com/resources/behrends-construction/behrend.pdf)
* Behrend, F. A., "On sets of integers which contain no three terms in arithmetical progression"
* [Wikipedia, *Salem-Spencer set*](https://en.wikipedia.org/wiki/Salem–Spencer_set)

## Tags

Salem-Spencer, Behrend construction, arithmetic progression, sphere, strictly convex
-/


open Finset Nat Real

open BigOperators Pointwise

namespace Behrend

variable {α β : Type _} {n d k N : ℕ} {x : Finₓ n → ℕ}

/-!
### Turning the sphere into a Salem-Spencer set

We define `behrend.sphere`, the intersection of the $$L^2$$ sphere with the positive quadrant of
integer points. Because the $$L^2$$ closed ball is strictly convex, the $$L^2$$ sphere and
`behrend.sphere` are Salem-Spencer (`add_salem_spencer_sphere`). Then we can turn this set in
`fin n → ℕ` into a set in `ℕ` using `behrend.map`, which preserves `add_salem_spencer` because it is
an additive monoid homomorphism.
-/


/-- The box `{0, ..., d - 1}^n` as a finset. -/
def box (n d : ℕ) : Finset (Finₓ n → ℕ) :=
  Fintype.piFinset fun _ => range d

theorem mem_box : x ∈ box n d ↔ ∀ i, x i < d := by
  simp only [← box, ← Fintype.mem_pi_finset, ← mem_range]

@[simp]
theorem card_box : (box n d).card = d ^ n := by
  simp [← box]

@[simp]
theorem box_zero : box (n + 1) 0 = ∅ := by
  simp [← box]

/-- The intersection of the sphere of radius `sqrt k` with the integer points in the positive
quadrant. -/
def sphere (n d k : ℕ) : Finset (Finₓ n → ℕ) :=
  (box n d).filter fun x => (∑ i, x i ^ 2) = k

theorem sphere_zero_subset : sphere n d 0 ⊆ 0 := fun x => by
  simp (config := { contextual := true })[← sphere, ← Function.funext_iffₓ]

@[simp]
theorem sphere_zero_right (n k : ℕ) : sphere (n + 1) 0 k = ∅ := by
  simp [← sphere]

theorem sphere_subset_box : sphere n d k ⊆ box n d :=
  filter_subset _ _

theorem norm_of_mem_sphere {x : Finₓ n → ℕ} (hx : x ∈ sphere n d k) :
    ∥(PiLp.equiv 2 _).symm (coe ∘ x : Finₓ n → ℝ)∥ = sqrt k := by
  rw [EuclideanSpace.norm_eq]
  dsimp'
  simp_rw [abs_cast, ← cast_pow, ← cast_sum, (mem_filter.1 hx).2]

theorem sphere_subset_preimage_metric_sphere :
    (sphere n d k : Set (Finₓ n → ℕ)) ⊆
      (fun x : Finₓ n → ℕ => (PiLp.equiv 2 _).symm (coe ∘ x : Finₓ n → ℝ)) ⁻¹'
        Metric.Sphere (0 : PiLp 2 fun _ : Finₓ n => ℝ) (sqrt k) :=
  fun x hx => by
  rw [Set.mem_preimage, mem_sphere_zero_iff_norm, norm_of_mem_sphere hx]

/-- The map that appears in Behrend's bound on Roth numbers. -/
@[simps]
def map (d : ℕ) : (Finₓ n → ℕ) →+ ℕ where
  toFun := fun a => ∑ i, a i * d ^ (i : ℕ)
  map_zero' := by
    simp_rw [Pi.zero_apply, zero_mul, sum_const_zero]
  map_add' := fun a b => by
    simp_rw [Pi.add_apply, add_mulₓ, sum_add_distrib]

@[simp]
theorem map_zero (d : ℕ) (a : Finₓ 0 → ℕ) : map d a = 0 := by
  simp [← map]

theorem map_succ (a : Finₓ (n + 1) → ℕ) : map d a = a 0 + (∑ x : Finₓ n, a x.succ * d ^ (x : ℕ)) * d := by
  simp [← map, ← Finₓ.sum_univ_succ, ← pow_succ'ₓ, mul_assoc, sum_mul]

theorem map_succ' (a : Finₓ (n + 1) → ℕ) : map d a = a 0 + map d (a ∘ Finₓ.succ) * d :=
  map_succ _

theorem map_monotone (d : ℕ) : Monotone (map d : (Finₓ n → ℕ) → ℕ) := fun x y h => by
  dsimp'
  exact sum_le_sum fun i _ => Nat.mul_le_mul_rightₓ _ <| h i

theorem map_mod (a : Finₓ n.succ → ℕ) : map d a % d = a 0 % d := by
  rw [map_succ, Nat.add_mul_mod_self_rightₓ]

theorem map_eq_iff {x₁ x₂ : Finₓ n.succ → ℕ} (hx₁ : ∀ i, x₁ i < d) (hx₂ : ∀ i, x₂ i < d) :
    map d x₁ = map d x₂ ↔ x₁ 0 = x₂ 0 ∧ map d (x₁ ∘ Finₓ.succ) = map d (x₂ ∘ Finₓ.succ) := by
  refine'
    ⟨fun h => _, fun h => by
      rw [map_succ', map_succ', h.1, h.2]⟩
  have : x₁ 0 = x₂ 0 := by
    rw [← mod_eq_of_lt (hx₁ _), ← map_mod, ← mod_eq_of_lt (hx₂ _), ← map_mod, h]
  rw [map_succ, map_succ, this, add_right_injₓ, mul_eq_mul_right_iff] at h
  exact ⟨this, h.resolve_right (pos_of_gt (hx₁ 0)).ne'⟩

theorem map_inj_on : { x : Finₓ n → ℕ | ∀ i, x i < d }.InjOn (map d) := by
  intro x₁ hx₁ x₂ hx₂ h
  induction' n with n ih
  · simp
    
  ext i
  have x := (map_eq_iff hx₁ hx₂).1 h
  refine' Finₓ.cases x.1 (congr_fun <| ih (fun _ => _) (fun _ => _) x.2) i
  · exact hx₁ _
    
  · exact hx₂ _
    

theorem map_le_of_mem_box (hx : x ∈ box n d) : map (2 * d - 1) x ≤ ∑ i : Finₓ n, (d - 1) * (2 * d - 1) ^ (i : ℕ) :=
  (map_monotone (2 * d - 1)) fun _ => Nat.le_pred_of_ltₓ <| mem_box.1 hx _

theorem add_salem_spencer_sphere : AddSalemSpencer (sphere n d k : Set (Finₓ n → ℕ)) := by
  set f : (Finₓ n → ℕ) →+ EuclideanSpace ℝ (Finₓ n) :=
    { toFun := fun f => (coe : ℕ → ℝ) ∘ f, map_zero' := funext fun _ => cast_zero,
      map_add' := fun _ _ => funext fun _ => cast_add _ _ }
  refine' AddSalemSpencer.of_image (f.to_add_freiman_hom (sphere n d k) 2) _ _
  · exact cast_injective.comp_left.inj_on _
    
  refine' (add_salem_spencer_sphere 0 <| sqrt k).mono (Set.image_subset_iff.2 fun x => _)
  rw [Set.mem_preimage, mem_sphere_zero_iff_norm]
  exact norm_of_mem_sphere

theorem add_salem_spencer_image_sphere : AddSalemSpencer ((sphere n d k).Image (map (2 * d - 1)) : Set ℕ) := by
  rw [coe_image]
  refine'
    @AddSalemSpencer.image _ (Finₓ n → ℕ) ℕ _ _ (sphere n d k) _ (map (2 * d - 1)) (map_inj_on.mono _)
      add_salem_spencer_sphere
  rw [Set.add_subset_iff]
  rintro a ha b hb i
  have hai := mem_box.1 (sphere_subset_box ha) i
  have hbi := mem_box.1 (sphere_subset_box hb) i
  rw [lt_tsub_iff_right, ← succ_le_iff, two_mul]
  exact (add_add_add_commₓ _ _ 1 1).trans_le (add_le_add hai hbi)

theorem sum_sq_le_of_mem_box (hx : x ∈ box n d) : (∑ i : Finₓ n, x i ^ 2) ≤ n * (d - 1) ^ 2 := by
  rw [mem_box] at hx
  have : ∀ i, x i ^ 2 ≤ (d - 1) ^ 2 := fun i => Nat.pow_le_pow_of_le_leftₓ (Nat.le_pred_of_ltₓ (hx i)) _
  exact
    ((sum_le_card_nsmul univ _ _) fun i _ => this i).trans
      (by
        rw [card_fin, smul_eq_mul])

theorem sum_eq : (∑ i : Finₓ n, d * (2 * d + 1) ^ (i : ℕ)) = ((2 * d + 1) ^ n - 1) / 2 := by
  refine' (Nat.div_eq_of_eq_mul_leftₓ zero_lt_two _).symm
  rw [← sum_range fun i => d * (2 * d + 1) ^ (i : ℕ), ← mul_sum, mul_right_commₓ, mul_comm d, ← geom_sum_mul_add,
    add_tsub_cancel_right, mul_comm]

theorem sum_lt : (∑ i : Finₓ n, d * (2 * d + 1) ^ (i : ℕ)) < (2 * d + 1) ^ n :=
  sum_eq.trans_lt <| (Nat.div_le_selfₓ _ 2).trans_lt <| pred_ltₓ (pow_pos (succ_posₓ _) _).ne'

theorem card_sphere_le_roth_number_nat (n d k : ℕ) : (sphere n d k).card ≤ rothNumberNat ((2 * d - 1) ^ n) := by
  cases n
  · refine' (card_le_univ _).trans_eq _
    rw [pow_zeroₓ]
    exact Fintype.card_unique
    
  cases d
  · simp
    
  refine' add_salem_spencer_image_sphere.le_roth_number_nat _ _ (card_image_of_inj_on _)
  · simp only [← subset_iff, ← mem_image, ← and_imp, ← forall_exists_index, ← mem_range, ← forall_apply_eq_imp_iff₂, ←
      sphere, ← mem_filter]
    rintro _ x hx _ rfl
    exact (map_le_of_mem_box hx).trans_lt sum_lt
    
  refine' map_inj_on.mono fun x => _
  simp only [← mem_coe, ← sphere, ← mem_filter, ← mem_box, ← and_imp, ← two_mul]
  exact fun h _ i => (h i).trans_le le_self_add

end Behrend

