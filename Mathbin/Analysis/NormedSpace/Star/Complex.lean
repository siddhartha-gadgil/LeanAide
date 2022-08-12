/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathbin.Analysis.NormedSpace.Star.Basic
import Mathbin.Algebra.Star.Module
import Mathbin.Analysis.Complex.Basic

/-!
# Complex normed star modules and algebras

Facts about star modules and star algebras over the complex numbers.

## Main definitions

* `star_module.mul_neg_I_lin`: multiplication by -I as a real-linear equivalence between the
  skew-adjoint and self-adjoint elements of a star module.
* `star_module.im`: the imaginary part of an element of a star module, defined via
  `skew_adjoint_part`.

-/


variable {E : Type _}

namespace StarModule

open ComplexConjugate

open Complex

variable [AddCommGroupₓ E] [StarAddMonoid E] [Module ℂ E] [StarModule ℂ E]

/-- Multiplication by -I as a real-linear equivalence between the skew-adjoint and self-adjoint
elements of a star module. -/
@[simps]
def mulNegILin : skewAdjoint E ≃ₗ[ℝ] selfAdjoint E where
  toFun := fun x =>
    ⟨-I • x, by
      simp [← selfAdjoint.mem_iff]⟩
  invFun := fun x =>
    ⟨I • x, by
      simp [← skewAdjoint.mem_iff]⟩
  map_add' := fun x y => by
    ext
    simp only [← AddSubgroup.coe_add, ← smul_add, ← AddSubgroup.coe_mk]
  map_smul' := fun r x => by
    ext
    simp only [← neg_smul, ← neg_inj, ← skewAdjoint.coe_smul, ← AddSubgroup.coe_mk, ← RingHom.id_apply, ←
      selfAdjoint.coe_smul, ← smul_neg, ← smul_comm I]
  left_inv := fun x => by
    simp only [← neg_smul, ← AddSubgroup.coe_mk, ← smul_neg, mul_smul, ← I_mul_I, ← neg_negₓ, ← one_smul, ← SetLike.eta]
  right_inv := fun x => by
    simp only [mul_smul, ← I_mul_I, ← AddSubgroup.coe_mk, ← neg_mul, ← neg_negₓ, ← one_smul, ← SetLike.eta]

/-- The imaginary part of an element of a star module, as a real-linear map.  -/
@[simps]
noncomputable def im : E →ₗ[ℝ] selfAdjoint E :=
  mulNegILin.toLinearMap.comp (skewAdjointPart ℝ)

/-- The real part of an element of a star module, as a real-linear map. This is simply an
abbreviation for `self_adjoint_part ℝ`. -/
@[simps]
noncomputable abbrev re : E →ₗ[ℝ] selfAdjoint E :=
  selfAdjointPart ℝ

/-- An element of a complex star module can be decomposed into self-adjoint "real" and
"imaginary" parts -/
theorem re_add_im (x : E) : (re x : E) + I • im x = x := by
  simp [mul_smul, ← I_mul_I, smul_add, two_smul ℝ]

end StarModule

