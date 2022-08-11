/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathbin.Topology.Algebra.Nonarchimedean.Bases
import Mathbin.Topology.Algebra.UniformFilterBasis
import Mathbin.RingTheory.Valuation.Basic

/-!
# The topology on a valued ring

In this file, we define the non archimedean topology induced by a valuation on a ring.
The main definition is a `valued` type class which equips a ring with a valuation taking
values in a group with zero. Other instances are then deduced from this.
-/


open Classical TopologicalSpace uniformity

open Set Valuation

noncomputable section

universe v u

variable {R : Type u} [Ringₓ R] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

variable (v : Valuation R Γ₀)

/-- The basis of open subgroups for the topology on a ring determined by a valuation. -/
theorem subgroups_basis : RingSubgroupsBasis fun γ : Γ₀ˣ => (v.ltAddSubgroup γ : AddSubgroup R) :=
  { inter := by
      rintro γ₀ γ₁
      use min γ₀ γ₁
      simp [← Valuation.ltAddSubgroup] <;> tauto,
    mul := by
      rintro γ
      cases' exists_square_le γ with γ₀ h
      use γ₀
      rintro - ⟨r, s, r_in, s_in, rfl⟩
      calc (v (r * s) : Γ₀) = v r * v s := Valuation.map_mul _ _ _ _ < γ₀ * γ₀ := mul_lt_mul₀ r_in s_in _ ≤ γ := by
          exact_mod_cast h,
    leftMul := by
      rintro x γ
      rcases GroupWithZeroₓ.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use (1 : Γ₀ˣ)
        rintro y (y_in : (v y : Γ₀) < 1)
        change v (x * y) < _
        rw [Valuation.map_mul, Hx, zero_mul]
        exact Units.zero_lt γ
        
      · simp only [← image_subset_iff, ← set_of_subset_set_of, ← preimage_set_of_eq, ← Valuation.map_mul]
        use γx⁻¹ * γ
        rintro y (vy_lt : v y < ↑(γx⁻¹ * γ))
        change (v (x * y) : Γ₀) < γ
        rw [Valuation.map_mul, Hx, mul_comm]
        rw [Units.coe_mul, mul_comm] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt
        ,
    rightMul := by
      rintro x γ
      rcases GroupWithZeroₓ.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use 1
        rintro y (y_in : (v y : Γ₀) < 1)
        change v (y * x) < _
        rw [Valuation.map_mul, Hx, mul_zero]
        exact Units.zero_lt γ
        
      · use γx⁻¹ * γ
        rintro y (vy_lt : v y < ↑(γx⁻¹ * γ))
        change (v (y * x) : Γ₀) < γ
        rw [Valuation.map_mul, Hx]
        rw [Units.coe_mul, mul_comm] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt
         }

end Valuation

/-- A valued ring is a ring that comes equipped with a distinguished valuation. The class `valued`
is designed for the situation that there is a canonical valuation on the ring.

TODO: show that there always exists an equivalent valuation taking values in a type belonging to
the same universe as the ring.

See Note [forgetful inheritance] for why we extend `uniform_space`, `uniform_add_group`. -/
class Valued (R : Type u) [Ringₓ R] (Γ₀ : outParam (Type v)) [LinearOrderedCommGroupWithZero Γ₀] extends UniformSpace R,
  UniformAddGroup R where
  V : Valuation R Γ₀
  is_topological_valuation : ∀ s, s ∈ 𝓝 (0 : R) ↔ ∃ γ : Γ₀ˣ, { x : R | v x < γ } ⊆ s

attribute [nolint dangerous_instance] Valued.toUniformSpace

namespace Valued

/-- Alternative `valued` constructor for use when there is no preferred `uniform_space`
structure. -/
def mk' (v : Valuation R Γ₀) : Valued R Γ₀ :=
  { V, toUniformSpace := @TopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _,
    to_uniform_add_group := @topological_add_group_is_uniform _ _ v.subgroups_basis.topology _,
    is_topological_valuation := by
      let this := @TopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _
      intro s
      rw [filter.has_basis_iff.mp v.subgroups_basis.has_basis_nhds_zero s]
      exact
        exists_congr fun γ => by
          simpa }

variable (R Γ₀) [_i : Valued R Γ₀]

include _i

theorem has_basis_nhds_zero : (𝓝 (0 : R)).HasBasis (fun _ => True) fun γ : Γ₀ˣ => { x | v x < (γ : Γ₀) } := by
  simp [← Filter.has_basis_iff, ← is_topological_valuation]

theorem has_basis_uniformity : (𝓤 R).HasBasis (fun _ => True) fun γ : Γ₀ˣ => { p : R × R | v (p.2 - p.1) < (γ : Γ₀) } :=
  by
  rw [uniformity_eq_comap_nhds_zero]
  exact (has_basis_nhds_zero R Γ₀).comap _

theorem to_uniform_space_eq : to_uniform_space = @TopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _ :=
  uniform_space_eq ((has_basis_uniformity R Γ₀).eq_of_same_basis <| v.subgroups_basis.has_basis_nhds_zero.comap _)

variable {R Γ₀}

theorem mem_nhds {s : Set R} {x : R} : s ∈ 𝓝 x ↔ ∃ γ : Γ₀ˣ, { y | (v (y - x) : Γ₀) < γ } ⊆ s := by
  simp only [nhds_translation_add_neg x, sub_eq_add_neg, ← preimage_set_of_eq, ← exists_true_left, ←
    ((has_basis_nhds_zero R Γ₀).comap fun y => y - x).mem_iff]

theorem mem_nhds_zero {s : Set R} : s ∈ 𝓝 (0 : R) ↔ ∃ γ : Γ₀ˣ, { x | v x < (γ : Γ₀) } ⊆ s := by
  simp only [← mem_nhds, ← sub_zero]

theorem loc_const {x : R} (h : (v x : Γ₀) ≠ 0) : { y : R | v y = v x } ∈ 𝓝 x := by
  rw [mem_nhds]
  rcases units.exists_iff_ne_zero.mpr h with ⟨γ, hx⟩
  use γ
  rw [hx]
  intro y y_in
  exact Valuation.map_eq_of_sub_lt _ y_in

instance (priority := 100) : TopologicalRing R :=
  (to_uniform_space_eq R Γ₀).symm ▸ v.subgroups_basis.toRingFilterBasis.is_topological_ring

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y «expr ∈ » M)
theorem cauchy_iff {F : Filter R} :
    Cauchy F ↔ F.ne_bot ∧ ∀ γ : Γ₀ˣ, ∃ M ∈ F, ∀ (x y) (_ : x ∈ M) (_ : y ∈ M), (v (y - x) : Γ₀) < γ := by
  rw [to_uniform_space_eq, AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [valued.v.subgroups_basis.mem_add_group_filter_basis_iff]
  constructor
  · intro h γ
    exact h _ (valued.v.subgroups_basis.mem_add_group_filter_basis _)
    
  · rintro h - ⟨γ, rfl⟩
    exact h γ
    

end Valued

