/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathbin.Data.Polynomial.Induction
import Mathbin.Data.Polynomial.Degree.Definitions

/-!  #  Interactions between `R[X]` and `Rᵐᵒᵖ[X]`

This file contains the basic API for "pushing through" the isomorphism
`op_ring_equiv : R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X]`.  It allows going back and forth between a polynomial ring
over a semiring and the polynomial ring over the opposite semiring. -/


open Polynomial

open Polynomial MulOpposite

variable {R : Type _} [Semiringₓ R] {p q : R[X]}

noncomputable section

namespace Polynomial

/-- Ring isomorphism between `R[X]ᵐᵒᵖ` and `Rᵐᵒᵖ[X]` sending each coefficient of a polynomial
to the corresponding element of the opposite ring. -/
def opRingEquiv (R : Type _) [Semiringₓ R] : R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X] :=
  ((toFinsuppIso R).op.trans AddMonoidAlgebra.opRingEquiv).trans (toFinsuppIso _).symm

/-!  Lemmas to get started, using `op_ring_equiv R` on the various expressions of
`finsupp.single`: `monomial`, `C a`, `X`, `C a * X ^ n`. -/


-- for maintenance purposes: `by simp [op_ring_equiv]` proves this lemma
@[simp]
theorem op_ring_equiv_op_monomial (n : ℕ) (r : R) : opRingEquiv R (op (monomial n r : R[X])) = monomial n (op r) := by
  simp only [← op_ring_equiv, ← RingEquiv.trans_apply, ← RingEquiv.op_apply_apply, ← RingEquiv.to_add_equiv_eq_coe, ←
    AddEquiv.mul_op_apply, ← AddEquiv.to_fun_eq_coe, ← AddEquiv.coe_trans, ← op_add_equiv_apply, ←
    RingEquiv.coe_to_add_equiv, ← op_add_equiv_symm_apply, ← Function.comp_app, ← unop_op, ← to_finsupp_iso_apply, ←
    to_finsupp_monomial, ← AddMonoidAlgebra.op_ring_equiv_single, ← to_finsupp_iso_symm_apply, ← of_finsupp_single]

@[simp]
theorem op_ring_equiv_op_C (a : R) : opRingEquiv R (op (c a)) = c (op a) :=
  op_ring_equiv_op_monomial 0 a

@[simp]
theorem op_ring_equiv_op_X : opRingEquiv R (op (x : R[X])) = X :=
  op_ring_equiv_op_monomial 1 1

theorem op_ring_equiv_op_C_mul_X_pow (r : R) (n : ℕ) : opRingEquiv R (op (c r * X ^ n : R[X])) = c (op r) * X ^ n := by
  simp only [← X_pow_mul, ← op_mul, ← op_pow, ← map_mul, ← map_pow, ← op_ring_equiv_op_X, ← op_ring_equiv_op_C]

/-!  Lemmas to get started, using `(op_ring_equiv R).symm` on the various expressions of
`finsupp.single`: `monomial`, `C a`, `X`, `C a * X ^ n`. -/


@[simp]
theorem op_ring_equiv_symm_monomial (n : ℕ) (r : Rᵐᵒᵖ) :
    (opRingEquiv R).symm (monomial n r) = op (monomial n (unop r)) :=
  (opRingEquiv R).Injective
    (by
      simp )

@[simp]
theorem op_ring_equiv_symm_C (a : Rᵐᵒᵖ) : (opRingEquiv R).symm (c a) = op (c (unop a)) :=
  op_ring_equiv_symm_monomial 0 a

@[simp]
theorem op_ring_equiv_symm_X : (opRingEquiv R).symm (x : Rᵐᵒᵖ[X]) = op x :=
  op_ring_equiv_symm_monomial 1 1

theorem op_ring_equiv_symm_C_mul_X_pow (r : Rᵐᵒᵖ) (n : ℕ) :
    (opRingEquiv R).symm (c r * X ^ n : Rᵐᵒᵖ[X]) = op (c (unop r) * X ^ n) := by
  rw [← monomial_eq_C_mul_X, op_ring_equiv_symm_monomial, monomial_eq_C_mul_X]

/-!  Lemmas about more global properties of polynomials and opposites. -/


@[simp]
theorem coeff_op_ring_equiv (p : R[X]ᵐᵒᵖ) (n : ℕ) : (opRingEquiv R p).coeff n = op ((unop p).coeff n) := by
  induction p using MulOpposite.rec
  cases p
  rfl

@[simp]
theorem support_op_ring_equiv (p : R[X]ᵐᵒᵖ) : (opRingEquiv R p).Support = (unop p).Support := by
  induction p using MulOpposite.rec
  cases p
  exact Finsupp.support_map_range_of_injective _ _ op_injective

@[simp]
theorem nat_degree_op_ring_equiv (p : R[X]ᵐᵒᵖ) : (opRingEquiv R p).natDegree = (unop p).natDegree := by
  by_cases' p0 : p = 0
  · simp only [← p0, ← _root_.map_zero, ← nat_degree_zero, ← unop_zero]
    
  · simp only [← p0, ← nat_degree_eq_support_max', ← Ne.def, ← AddEquivClass.map_eq_zero_iff, ← not_false_iff, ←
      support_op_ring_equiv, ← unop_eq_zero_iff]
    

@[simp]
theorem leading_coeff_op_ring_equiv (p : R[X]ᵐᵒᵖ) : (opRingEquiv R p).leadingCoeff = op (unop p).leadingCoeff := by
  rw [leading_coeff, coeff_op_ring_equiv, nat_degree_op_ring_equiv, leading_coeff]

end Polynomial

