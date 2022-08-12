/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathbin.Analysis.Normed.Group.Hom
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Analysis.NormedSpace.LinearIsometry
import Mathbin.Algebra.Star.SelfAdjoint
import Mathbin.Algebra.Star.Unitary

/-!
# Normed star rings and algebras

A normed star group is a normed group with a compatible `star` which is isometric.

A C⋆-ring is a normed star group that is also a ring and that verifies the stronger
condition `∥x⋆ * x∥ = ∥x∥^2` for all `x`.  If a C⋆-ring is also a star algebra, then it is a
C⋆-algebra.

To get a C⋆-algebra `E` over field `𝕜`, use
`[normed_field 𝕜] [star_ring 𝕜] [normed_ring E] [star_ring E] [cstar_ring E]
 [normed_algebra 𝕜 E] [star_module 𝕜 E]`.

## TODO

- Show that `∥x⋆ * x∥ = ∥x∥^2` is equivalent to `∥x⋆ * x∥ = ∥x⋆∥ * ∥x∥`, which is used as the
  definition of C*-algebras in some sources (e.g. Wikipedia).

-/


open TopologicalSpace

-- mathport name: «expr ⋆»
local postfix:max "⋆" => star

/-- A normed star group is a normed group with a compatible `star` which is isometric. -/
class NormedStarGroup (E : Type _) [SemiNormedGroup E] [StarAddMonoid E] : Prop where
  norm_star : ∀ x : E, ∥x⋆∥ = ∥x∥

export NormedStarGroup (norm_star)

attribute [simp] norm_star

variable {𝕜 E α : Type _}

section NormedStarGroup

variable [SemiNormedGroup E] [StarAddMonoid E] [NormedStarGroup E]

@[simp]
theorem nnnorm_star (x : E) : ∥star x∥₊ = ∥x∥₊ :=
  Subtype.ext <| norm_star _

/-- The `star` map in a normed star group is a normed group homomorphism. -/
def starNormedGroupHom : NormedGroupHom E E :=
  { starAddEquiv with bound' := ⟨1, fun v => le_transₓ (norm_star _).le (one_mulₓ _).symm.le⟩ }

/-- The `star` map in a normed star group is an isometry -/
theorem star_isometry : Isometry (star : E → E) :=
  show Isometry starAddEquiv from AddMonoidHomClass.isometry_of_norm starAddEquiv (show ∀ x, ∥x⋆∥ = ∥x∥ from norm_star)

instance (priority := 100) NormedStarGroup.to_has_continuous_star : HasContinuousStar E :=
  ⟨star_isometry.Continuous⟩

end NormedStarGroup

instance RingHomIsometric.star_ring_end [NormedCommRing E] [StarRing E] [NormedStarGroup E] :
    RingHomIsometric (starRingEnd E) :=
  ⟨norm_star⟩

/-- A C*-ring is a normed star ring that satifies the stronger condition `∥x⋆ * x∥ = ∥x∥^2`
for every `x`. -/
class CstarRing (E : Type _) [NonUnitalNormedRing E] [StarRing E] : Prop where
  norm_star_mul_self : ∀ {x : E}, ∥x⋆ * x∥ = ∥x∥ * ∥x∥

instance :
    CstarRing ℝ where norm_star_mul_self := fun x => by
    simp only [← star, ← id.def, ← norm_mul]

namespace CstarRing

section NonUnital

variable [NonUnitalNormedRing E] [StarRing E] [CstarRing E]

/-- In a C*-ring, star preserves the norm. -/
-- see Note [lower instance priority]
instance (priority := 100) to_normed_star_group : NormedStarGroup E :=
  ⟨by
    intro x
    by_cases' htriv : x = 0
    · simp only [← htriv, ← star_zero]
      
    · have hnt : 0 < ∥x∥ := norm_pos_iff.mpr htriv
      have hnt_star : 0 < ∥x⋆∥ := norm_pos_iff.mpr ((AddEquiv.map_ne_zero_iff starAddEquiv).mpr htriv)
      have h₁ :=
        calc
          ∥x∥ * ∥x∥ = ∥x⋆ * x∥ := norm_star_mul_self.symm
          _ ≤ ∥x⋆∥ * ∥x∥ := norm_mul_le _ _
          
      have h₂ :=
        calc
          ∥x⋆∥ * ∥x⋆∥ = ∥x * x⋆∥ := by
            rw [← norm_star_mul_self, star_star]
          _ ≤ ∥x∥ * ∥x⋆∥ := norm_mul_le _ _
          
      exact le_antisymmₓ (le_of_mul_le_mul_right h₂ hnt_star) (le_of_mul_le_mul_right h₁ hnt)
      ⟩

theorem norm_self_mul_star {x : E} : ∥x * x⋆∥ = ∥x∥ * ∥x∥ := by
  nth_rw 0[← star_star x]
  simp only [← norm_star_mul_self, ← norm_star]

theorem norm_star_mul_self' {x : E} : ∥x⋆ * x∥ = ∥x⋆∥ * ∥x∥ := by
  rw [norm_star_mul_self, norm_star]

theorem nnnorm_star_mul_self {x : E} : ∥x⋆ * x∥₊ = ∥x∥₊ * ∥x∥₊ :=
  Subtype.ext norm_star_mul_self

end NonUnital

section Unital

variable [NormedRing E] [StarRing E] [CstarRing E]

@[simp]
theorem norm_one [Nontrivial E] : ∥(1 : E)∥ = 1 := by
  have : 0 < ∥(1 : E)∥ := norm_pos_iff.mpr one_ne_zero
  rw [← mul_left_inj' this.ne', ← norm_star_mul_self, mul_oneₓ, star_one, one_mulₓ]

-- see Note [lower instance priority]
instance (priority := 100) [Nontrivial E] : NormOneClass E :=
  ⟨norm_one⟩

theorem norm_coe_unitary [Nontrivial E] (U : unitary E) : ∥(U : E)∥ = 1 := by
  rw [← sq_eq_sq (norm_nonneg _) zero_le_one, one_pow 2, sq, ← CstarRing.norm_star_mul_self, unitary.coe_star_mul_self,
    CstarRing.norm_one]

@[simp]
theorem norm_of_mem_unitary [Nontrivial E] {U : E} (hU : U ∈ unitary E) : ∥U∥ = 1 :=
  norm_coe_unitary ⟨U, hU⟩

@[simp]
theorem norm_coe_unitary_mul (U : unitary E) (A : E) : ∥(U : E) * A∥ = ∥A∥ := by
  nontriviality E
  refine' le_antisymmₓ _ _
  · calc _ ≤ ∥(U : E)∥ * ∥A∥ := norm_mul_le _ _ _ = ∥A∥ := by
        rw [norm_coe_unitary, one_mulₓ]
    
  · calc _ = ∥(U : E)⋆ * U * A∥ := by
        rw [unitary.coe_star_mul_self U, one_mulₓ]_ ≤ ∥(U : E)⋆∥ * ∥(U : E) * A∥ := by
        rw [mul_assoc]
        exact norm_mul_le _ _ _ = ∥(U : E) * A∥ := by
        rw [norm_star, norm_coe_unitary, one_mulₓ]
    

@[simp]
theorem norm_unitary_smul (U : unitary E) (A : E) : ∥U • A∥ = ∥A∥ :=
  norm_coe_unitary_mul U A

theorem norm_mem_unitary_mul {U : E} (A : E) (hU : U ∈ unitary E) : ∥U * A∥ = ∥A∥ :=
  norm_coe_unitary_mul ⟨U, hU⟩ A

@[simp]
theorem norm_mul_coe_unitary (A : E) (U : unitary E) : ∥A * U∥ = ∥A∥ :=
  calc
    _ = ∥((U : E)⋆ * A⋆)⋆∥ := by
      simp only [← star_star, ← star_mul]
    _ = ∥(U : E)⋆ * A⋆∥ := by
      rw [norm_star]
    _ = ∥A⋆∥ := norm_mem_unitary_mul (star A) (unitary.star_mem U.Prop)
    _ = ∥A∥ := norm_star _
    

theorem norm_mul_mem_unitary (A : E) {U : E} (hU : U ∈ unitary E) : ∥A * U∥ = ∥A∥ :=
  norm_mul_coe_unitary A ⟨U, hU⟩

end Unital

end CstarRing

theorem nnnorm_pow_two_pow_of_self_adjoint [NormedRing E] [StarRing E] [CstarRing E] {x : E} (hx : x ∈ selfAdjoint E)
    (n : ℕ) : ∥x ^ 2 ^ n∥₊ = ∥x∥₊ ^ 2 ^ n := by
  induction' n with k hk
  · simp only [← pow_zeroₓ, ← pow_oneₓ]
    
  · rw [pow_succₓ, pow_mul', sq]
    nth_rw 0[← self_adjoint.mem_iff.mp hx]
    rw [← star_pow, CstarRing.nnnorm_star_mul_self, ← sq, hk, pow_mul']
    

theorem selfAdjoint.nnnorm_pow_two_pow [NormedRing E] [StarRing E] [CstarRing E] (x : selfAdjoint E) (n : ℕ) :
    ∥x ^ 2 ^ n∥₊ = ∥x∥₊ ^ 2 ^ n :=
  nnnorm_pow_two_pow_of_self_adjoint x.property _

section starₗᵢ

variable [CommSemiringₓ 𝕜] [StarRing 𝕜]

variable [SemiNormedGroup E] [StarAddMonoid E] [NormedStarGroup E]

variable [Module 𝕜 E] [StarModule 𝕜 E]

variable (𝕜)

/-- `star` bundled as a linear isometric equivalence -/
def starₗᵢ : E ≃ₗᵢ⋆[𝕜] E :=
  { starAddEquiv with map_smul' := star_smul, norm_map' := norm_star }

variable {𝕜}

@[simp]
theorem coe_starₗᵢ : (starₗᵢ 𝕜 : E → E) = star :=
  rfl

theorem starₗᵢ_apply {x : E} : starₗᵢ 𝕜 x = star x :=
  rfl

end starₗᵢ

