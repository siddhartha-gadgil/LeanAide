/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathbin.Topology.Algebra.Module.WeakDual
import Mathbin.Algebra.Algebra.Spectrum

/-!
# Character space of a topological algebra

The character space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. This space is used in the Gelfand transform, which gives an
isomorphism between a commutative C⋆-algebra and continuous functions on the character space
of the algebra. This, in turn, is used to construct the continuous functional calculus on
C⋆-algebras.


## Implementation notes

We define `character_space 𝕜 A` as a subset of the weak dual, which automatically puts the
correct topology on the space. We then define `to_alg_hom` which provides the algebra homomorphism
corresponding to any element. We also provide `to_clm` which provides the element as a
continuous linear map. (Even though `weak_dual 𝕜 A` is a type copy of `A →L[𝕜] 𝕜`, this is
often more convenient.)

## Tags

character space, Gelfand transform, functional calculus

-/


namespace WeakDual

/-- The character space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. -/
def CharacterSpace (𝕜 : Type _) (A : Type _) [CommSemiringₓ 𝕜] [TopologicalSpace 𝕜] [HasContinuousAdd 𝕜]
    [HasContinuousConstSmul 𝕜 𝕜] [NonUnitalNonAssocSemiringₓ A] [TopologicalSpace A] [Module 𝕜 A] :=
  { φ : WeakDual 𝕜 A | φ ≠ 0 ∧ ∀ x y : A, φ (x * y) = φ x * φ y }

variable {𝕜 : Type _} {A : Type _}

namespace CharacterSpace

section NonUnitalNonAssocSemiringₓ

variable [CommSemiringₓ 𝕜] [TopologicalSpace 𝕜] [HasContinuousAdd 𝕜] [HasContinuousConstSmul 𝕜 𝕜]
  [NonUnitalNonAssocSemiringₓ A] [TopologicalSpace A] [Module 𝕜 A]

theorem coe_apply (φ : CharacterSpace 𝕜 A) (x : A) : (φ : WeakDual 𝕜 A) x = φ x :=
  rfl

/-- An element of the character space, as a continuous linear map. -/
def toClm (φ : CharacterSpace 𝕜 A) : A →L[𝕜] 𝕜 :=
  (φ : WeakDual 𝕜 A)

theorem to_clm_apply (φ : CharacterSpace 𝕜 A) (x : A) : φ x = toClm φ x :=
  rfl

/-- An element of the character space, as an non-unital algebra homomorphism. -/
@[simps]
def toNonUnitalAlgHom (φ : CharacterSpace 𝕜 A) : A →ₙₐ[𝕜] 𝕜 where
  toFun := (φ : A → 𝕜)
  map_mul' := φ.Prop.2
  map_smul' := (toClm φ).map_smul
  map_zero' := ContinuousLinearMap.map_zero _
  map_add' := ContinuousLinearMap.map_add _

theorem map_zero (φ : CharacterSpace 𝕜 A) : φ 0 = 0 :=
  (toNonUnitalAlgHom φ).map_zero

theorem map_add (φ : CharacterSpace 𝕜 A) (x y : A) : φ (x + y) = φ x + φ y :=
  (toNonUnitalAlgHom φ).map_add _ _

theorem map_smul (φ : CharacterSpace 𝕜 A) (r : 𝕜) (x : A) : φ (r • x) = r • φ x :=
  (toClm φ).map_smul _ _

theorem map_mul (φ : CharacterSpace 𝕜 A) (x y : A) : φ (x * y) = φ x * φ y :=
  (toNonUnitalAlgHom φ).map_mul _ _

theorem continuous (φ : CharacterSpace 𝕜 A) : Continuous φ :=
  (toClm φ).Continuous

end NonUnitalNonAssocSemiringₓ

section Unital

variable [CommRingₓ 𝕜] [NoZeroDivisors 𝕜] [TopologicalSpace 𝕜] [HasContinuousAdd 𝕜] [HasContinuousConstSmul 𝕜 𝕜]
  [TopologicalSpace A] [Semiringₓ A] [Algebra 𝕜 A]

theorem map_one (φ : CharacterSpace 𝕜 A) : φ 1 = 1 := by
  have h₁ : φ 1 * (1 - φ 1) = 0 := by
    rw [mul_sub, sub_eq_zero, mul_oneₓ, ← map_mul φ, one_mulₓ]
  rcases mul_eq_zero.mp h₁ with (h₂ | h₂)
  · exfalso
    apply φ.prop.1
    ext
    rw [ContinuousLinearMap.zero_apply, ← one_mulₓ x, coe_apply, map_mul φ, h₂, zero_mul]
    
  · rw [sub_eq_zero] at h₂
    exact h₂.symm
    

/-- An element of the character space, as an algebra homomorphism. -/
@[simps]
def toAlgHom (φ : CharacterSpace 𝕜 A) : A →ₐ[𝕜] 𝕜 :=
  { toNonUnitalAlgHom φ with map_one' := map_one φ,
    commutes' := fun r => by
      rw [Algebra.algebra_map_eq_smul_one, Algebra.id.map_eq_id, RingHom.id_apply]
      change ((φ : WeakDual 𝕜 A) : A →L[𝕜] 𝕜) (r • 1) = r
      rw [ContinuousLinearMap.map_smul, Algebra.id.smul_eq_mul, coe_apply, map_one φ, mul_oneₓ] }

theorem eq_set_map_one_map_mul [Nontrivial 𝕜] :
    CharacterSpace 𝕜 A = { φ : WeakDual 𝕜 A | φ 1 = 1 ∧ ∀ x y : A, φ (x * y) = φ x * φ y } := by
  ext x
  refine' ⟨fun h => ⟨map_one ⟨x, h⟩, h.2⟩, fun h => ⟨_, h.2⟩⟩
  rintro rfl
  simpa using h.1

theorem is_closed [Nontrivial 𝕜] [T2Space 𝕜] [HasContinuousMul 𝕜] : IsClosed (CharacterSpace 𝕜 A) := by
  rw [eq_set_map_one_map_mul]
  refine' IsClosed.inter (is_closed_eq (eval_continuous _) continuous_const) _
  change IsClosed { φ : WeakDual 𝕜 A | ∀ x y : A, φ (x * y) = φ x * φ y }
  rw [Set.set_of_forall]
  refine' is_closed_Inter fun a => _
  rw [Set.set_of_forall]
  exact is_closed_Inter fun _ => is_closed_eq (eval_continuous _) ((eval_continuous _).mul (eval_continuous _))

end Unital

section Ringₓ

variable [CommRingₓ 𝕜] [NoZeroDivisors 𝕜] [TopologicalSpace 𝕜] [HasContinuousAdd 𝕜] [HasContinuousConstSmul 𝕜 𝕜]
  [TopologicalSpace A] [Ringₓ A] [Algebra 𝕜 A]

theorem apply_mem_spectrum [Nontrivial 𝕜] (φ : CharacterSpace 𝕜 A) (a : A) : φ a ∈ Spectrum 𝕜 a :=
  (toAlgHom φ).apply_mem_spectrum a

end Ringₓ

end CharacterSpace

end WeakDual

