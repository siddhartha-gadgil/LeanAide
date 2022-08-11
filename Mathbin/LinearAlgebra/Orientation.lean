/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathbin.LinearAlgebra.Ray
import Mathbin.LinearAlgebra.Determinant

/-!
# Orientations of modules

This file defines orientations of modules.

## Main definitions

* `orientation` is a type synonym for `module.ray` for the case where the module is that of
alternating maps from a module to its underlying ring.  An orientation may be associated with an
alternating map or with a basis.

* `module.oriented` is a type class for a choice of orientation of a module that is considered
the positive orientation.

## Implementation notes

`orientation` is defined for an arbitrary index type, but the main intended use case is when
that index type is a `fintype` and there exists a basis of the same cardinality.

## References

* https://en.wikipedia.org/wiki/Orientation_(vector_space)

-/


noncomputable section

open BigOperators

section OrderedCommSemiring

variable (R : Type _) [OrderedCommSemiring R]

variable (M : Type _) [AddCommMonoidₓ M] [Module R M]

variable {N : Type _} [AddCommMonoidₓ N] [Module R N]

variable (ι : Type _) [DecidableEq ι]

/-- An orientation of a module, intended to be used when `ι` is a `fintype` with the same
cardinality as a basis. -/
abbrev Orientation :=
  Module.Ray R (AlternatingMap R M R ι)

/-- A type class fixing an orientation of a module. -/
class Module.Oriented where
  positiveOrientation : Orientation R M ι

variable {R M}

/-- An equivalence between modules implies an equivalence between orientations. -/
def Orientation.map (e : M ≃ₗ[R] N) : Orientation R M ι ≃ Orientation R N ι :=
  Module.Ray.map <| AlternatingMap.domLcongr R R ι R e

@[simp]
theorem Orientation.map_apply (e : M ≃ₗ[R] N) (v : AlternatingMap R M R ι) (hv : v ≠ 0) :
    Orientation.map ι e (rayOfNeZero _ v hv) =
      rayOfNeZero _ (v.compLinearMap e.symm) (mt (v.comp_linear_equiv_eq_zero_iff e.symm).mp hv) :=
  rfl

@[simp]
theorem Orientation.map_refl : (Orientation.map ι <| LinearEquiv.refl R M) = Equivₓ.refl _ := by
  rw [Orientation.map, AlternatingMap.dom_lcongr_refl, Module.Ray.map_refl]

@[simp]
theorem Orientation.map_symm (e : M ≃ₗ[R] N) : (Orientation.map ι e).symm = Orientation.map ι e.symm :=
  rfl

end OrderedCommSemiring

section OrderedCommRing

variable {R : Type _} [OrderedCommRing R]

variable {M N : Type _} [AddCommGroupₓ M] [AddCommGroupₓ N] [Module R M] [Module R N]

namespace Basis

variable {ι : Type _} [Fintype ι] [DecidableEq ι]

/-- The orientation given by a basis. -/
protected def orientation [Nontrivial R] (e : Basis ι R M) : Orientation R M ι :=
  rayOfNeZero R _ e.det_ne_zero

theorem orientation_map [Nontrivial R] (e : Basis ι R M) (f : M ≃ₗ[R] N) :
    (e.map f).Orientation = Orientation.map ι f e.Orientation := by
  simp_rw [Basis.orientation, Orientation.map_apply, Basis.det_map']

/-- The value of `orientation.map` when the index type has the cardinality of a basis, in terms
of `f.det`. -/
theorem map_orientation_eq_det_inv_smul (e : Basis ι R M) (x : Orientation R M ι) (f : M ≃ₗ[R] M) :
    Orientation.map ι f x = f.det⁻¹ • x := by
  induction' x using Module.Ray.ind with g hg
  rw [Orientation.map_apply, smul_ray_of_ne_zero, ray_eq_iff, Units.smul_def,
    (g.comp_linear_map ↑f.symm).eq_smul_basis_det e, g.eq_smul_basis_det e, AlternatingMap.comp_linear_map_apply,
    AlternatingMap.smul_apply, Basis.det_comp, Basis.det_self, mul_oneₓ, smul_eq_mul, mul_comm, mul_smul,
    LinearEquiv.coe_inv_det]

/-- The orientation given by a basis derived using `units_smul`, in terms of the product of those
units. -/
theorem orientation_units_smul [Nontrivial R] (e : Basis ι R M) (w : ι → Units R) :
    (e.units_smul w).Orientation = (∏ i, w i)⁻¹ • e.Orientation := by
  rw [Basis.orientation, Basis.orientation, smul_ray_of_ne_zero, ray_eq_iff, e.det.eq_smul_basis_det (e.units_smul w),
    det_units_smul, Units.smul_def, smul_smul]
  norm_cast
  simp

end Basis

end OrderedCommRing

section LinearOrderedCommRing

variable {R : Type _} [LinearOrderedCommRing R]

variable {M : Type _} [AddCommGroupₓ M] [Module R M]

variable {ι : Type _} [DecidableEq ι]

namespace Basis

variable [Fintype ι]

/-- The orientations given by two bases are equal if and only if the determinant of one basis
with respect to the other is positive. -/
theorem orientation_eq_iff_det_pos (e₁ e₂ : Basis ι R M) : e₁.Orientation = e₂.Orientation ↔ 0 < e₁.det e₂ :=
  calc
    e₁.Orientation = e₂.Orientation ↔ SameRay R e₁.det e₂.det := ray_eq_iff _ _
    _ ↔ SameRay R (e₁.det e₂ • e₂.det) e₂.det := by
      rw [← e₁.det.eq_smul_basis_det e₂]
    _ ↔ 0 < e₁.det e₂ := same_ray_smul_left_iff_of_ne e₂.det_ne_zero (e₁.is_unit_det e₂).ne_zero
    

/-- Given a basis, any orientation equals the orientation given by that basis or its negation. -/
theorem orientation_eq_or_eq_neg (e : Basis ι R M) (x : Orientation R M ι) : x = e.Orientation ∨ x = -e.Orientation :=
  by
  induction' x using Module.Ray.ind with x hx
  rw [← x.map_basis_ne_zero_iff e] at hx
  rwa [Basis.orientation, ray_eq_iff, neg_ray_of_ne_zero, ray_eq_iff, x.eq_smul_basis_det e,
    same_ray_neg_smul_left_iff_of_ne e.det_ne_zero hx, same_ray_smul_left_iff_of_ne e.det_ne_zero hx, lt_or_lt_iff_ne,
    ne_comm]

/-- Given a basis, an orientation equals the negation of that given by that basis if and only
if it does not equal that given by that basis. -/
theorem orientation_ne_iff_eq_neg (e : Basis ι R M) (x : Orientation R M ι) : x ≠ e.Orientation ↔ x = -e.Orientation :=
  ⟨fun h => (e.orientation_eq_or_eq_neg x).resolve_left h, fun h =>
    h.symm ▸ (Module.Ray.ne_neg_self e.Orientation).symm⟩

/-- Composing a basis with a linear equiv gives the same orientation if and only if the
determinant is positive. -/
theorem orientation_comp_linear_equiv_eq_iff_det_pos (e : Basis ι R M) (f : M ≃ₗ[R] M) :
    (e.map f).Orientation = e.Orientation ↔ 0 < (f : M →ₗ[R] M).det := by
  rw [orientation_map, e.map_orientation_eq_det_inv_smul, units_inv_smul, units_smul_eq_self_iff, LinearEquiv.coe_det]

/-- Composing a basis with a linear equiv gives the negation of that orientation if and only if
the determinant is negative. -/
theorem orientation_comp_linear_equiv_eq_neg_iff_det_neg (e : Basis ι R M) (f : M ≃ₗ[R] M) :
    (e.map f).Orientation = -e.Orientation ↔ (f : M →ₗ[R] M).det < 0 := by
  rw [orientation_map, e.map_orientation_eq_det_inv_smul, units_inv_smul, units_smul_eq_neg_iff, LinearEquiv.coe_det]

/-- Negating a single basis vector (represented using `units_smul`) negates the corresponding
orientation. -/
@[simp]
theorem orientation_neg_single [Nontrivial R] (e : Basis ι R M) (i : ι) :
    (e.units_smul (Function.update 1 i (-1))).Orientation = -e.Orientation := by
  rw [orientation_units_smul, Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp

/-- Given a basis and an orientation, return a basis giving that orientation: either the original
basis, or one constructed by negating a single (arbitrary) basis vector. -/
def adjustToOrientation [Nontrivial R] [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι) : Basis ι R M :=
  have := Classical.decEq (Orientation R M ι)
  if e.orientation = x then e else e.units_smul (Function.update 1 (Classical.arbitrary ι) (-1))

/-- `adjust_to_orientation` gives a basis with the required orientation. -/
@[simp]
theorem orientation_adjust_to_orientation [Nontrivial R] [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι) :
    (e.adjustToOrientation x).Orientation = x := by
  rw [adjust_to_orientation]
  split_ifs with h
  · exact h
    
  · rw [orientation_neg_single, eq_comm, ← orientation_ne_iff_eq_neg, ne_comm]
    exact h
    

/-- Every basis vector from `adjust_to_orientation` is either that from the original basis or its
negation. -/
theorem adjust_to_orientation_apply_eq_or_eq_neg [Nontrivial R] [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι)
    (i : ι) : e.adjustToOrientation x i = e i ∨ e.adjustToOrientation x i = -e i := by
  rw [adjust_to_orientation]
  split_ifs with h
  · simp
    
  · by_cases' hi : i = Classical.arbitrary ι <;> simp [← units_smul_apply, ← hi]
    

end Basis

end LinearOrderedCommRing

section LinearOrderedField

variable {R : Type _} [LinearOrderedField R]

variable {M : Type _} [AddCommGroupₓ M] [Module R M]

variable {ι : Type _} [DecidableEq ι]

namespace Orientation

variable [Fintype ι] [FiniteDimensional R M]

open FiniteDimensional

/-- If the index type has cardinality equal to the finite dimension, any two orientations are
equal or negations. -/
theorem eq_or_eq_neg (x₁ x₂ : Orientation R M ι) (h : Fintype.card ι = finrank R M) : x₁ = x₂ ∨ x₁ = -x₂ := by
  have e := (fin_basis R M).reindex (Fintype.equivFinOfCardEq h).symm
  rcases e.orientation_eq_or_eq_neg x₁ with (h₁ | h₁) <;>
    rcases e.orientation_eq_or_eq_neg x₂ with (h₂ | h₂) <;> simp [← h₁, ← h₂]

/-- If the index type has cardinality equal to the finite dimension, an orientation equals the
negation of another orientation if and only if they are not equal. -/
theorem ne_iff_eq_neg (x₁ x₂ : Orientation R M ι) (h : Fintype.card ι = finrank R M) : x₁ ≠ x₂ ↔ x₁ = -x₂ :=
  ⟨fun hn => (eq_or_eq_neg x₁ x₂ h).resolve_left hn, fun he => he.symm ▸ (Module.Ray.ne_neg_self x₂).symm⟩

/-- The value of `orientation.map` when the index type has cardinality equal to the finite
dimension, in terms of `f.det`. -/
theorem map_eq_det_inv_smul (x : Orientation R M ι) (f : M ≃ₗ[R] M) (h : Fintype.card ι = finrank R M) :
    Orientation.map ι f x = f.det⁻¹ • x := by
  have e := (fin_basis R M).reindex (Fintype.equivFinOfCardEq h).symm
  exact e.map_orientation_eq_det_inv_smul x f

/-- If the index type has cardinality equal to the finite dimension, composing an alternating
map with the same linear equiv on each argument gives the same orientation if and only if the
determinant is positive. -/
theorem map_eq_iff_det_pos (x : Orientation R M ι) (f : M ≃ₗ[R] M) (h : Fintype.card ι = finrank R M) :
    Orientation.map ι f x = x ↔ 0 < (f : M →ₗ[R] M).det := by
  rw [map_eq_det_inv_smul _ _ h, units_inv_smul, units_smul_eq_self_iff, LinearEquiv.coe_det]

/-- If the index type has cardinality equal to the finite dimension, composing an alternating
map with the same linear equiv on each argument gives the negation of that orientation if and
only if the determinant is negative. -/
theorem map_eq_neg_iff_det_neg (x : Orientation R M ι) (f : M ≃ₗ[R] M) (h : Fintype.card ι = finrank R M) :
    Orientation.map ι f x = -x ↔ (f : M →ₗ[R] M).det < 0 := by
  rw [map_eq_det_inv_smul _ _ h, units_inv_smul, units_smul_eq_neg_iff, LinearEquiv.coe_det]

/-- If the index type has cardinality equal to the finite dimension, a basis with the given
orientation. -/
def someBasis [Nonempty ι] (x : Orientation R M ι) (h : Fintype.card ι = finrank R M) : Basis ι R M :=
  ((finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm).adjustToOrientation x

/-- `some_basis` gives a basis with the required orientation. -/
@[simp]
theorem some_basis_orientation [Nonempty ι] (x : Orientation R M ι) (h : Fintype.card ι = finrank R M) :
    (x.someBasis h).Orientation = x :=
  Basis.orientation_adjust_to_orientation _ _

end Orientation

end LinearOrderedField

