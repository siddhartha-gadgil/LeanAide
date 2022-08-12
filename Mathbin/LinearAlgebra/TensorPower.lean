/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.LinearAlgebra.PiTensorProduct
import Mathbin.Logic.Equiv.Fin
import Mathbin.Algebra.DirectSum.Algebra

/-!
# Tensor power of a semimodule over a commutative semirings

We define the `n`th tensor power of `M` as the n-ary tensor product indexed by `fin n` of `M`,
`⨂[R] (i : fin n), M`. This is a special case of `pi_tensor_product`.

This file introduces the notation `⨂[R]^n M` for `tensor_power R n M`, which in turn is an
abbreviation for `⨂[R] i : fin n, M`.

## Main definitions:

* `tensor_power.ghas_one`
* `tensor_power.ghas_mul`

## TODO

Show `direct_sum.galgebra R (λ i, ⨂[R]^i M)` and `algebra R (⨁ n : ℕ, ⨂[R]^n M)`.


## Implementation notes

In this file we use `ₜ1` and `ₜ*` as local notation for the graded multiplicative structure on
tensor powers. Elsewhere, using `1` and `*` on `graded_monoid` should be preferred.
-/


open TensorProduct

/-- Homogenous tensor powers $M^{\otimes n}$. `⨂[R]^n M` is a shorthand for
`⨂[R] (i : fin n), M`. -/
@[reducible]
protected def TensorPower (R : Type _) (n : ℕ) (M : Type _) [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] :
    Type _ :=
  ⨂[R] i : Finₓ n, M

variable {R : Type _} {M : Type _} [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M]

-- mathport name: «expr⨂[ ]^ »
localized [TensorProduct] notation:100 "⨂[" R "]^" n:arg => TensorPower R n

namespace TensorPower

open TensorProduct DirectSum

open PiTensorProduct

/-- As a graded monoid, `⨂[R]^i M` has a `1 : ⨂[R]^0 M`. -/
instance ghasOne : GradedMonoid.GhasOne fun i => (⨂[R]^i) M where one := tprod R Finₓ.elim0

-- mathport name: «exprₜ1»
local notation "ₜ1" => @GradedMonoid.GhasOne.one ℕ (fun i => (⨂[R]^i) M) _ _

theorem ghas_one_def : ₜ1 = tprod R Finₓ.elim0 :=
  rfl

/-- A variant of `pi_tensor_prod.tmul_equiv` with the result indexed by `fin (n + m)`. -/
def mulEquiv {n m : ℕ} : (⨂[R]^n) M ⊗[R] (⨂[R]^m) M ≃ₗ[R] (⨂[R]^(n + m)) M :=
  (tmulEquiv R M).trans (reindex R M finSumFinEquiv)

/-- As a graded monoid, `⨂[R]^i M` has a `(*) : ⨂[R]^i M → ⨂[R]^j M → ⨂[R]^(i + j) M`. -/
instance ghasMul : GradedMonoid.GhasMul fun i => (⨂[R]^i) M where mul := fun i j a b => mulEquiv (a ⊗ₜ b)

-- mathport name: «expr ₜ* »
local infixl:70 "ₜ*" => @GradedMonoid.GhasMul.mul ℕ (fun i => (⨂[R]^i) M) _ _ _ _

theorem ghas_mul_def {i j} (a : (⨂[R]^i) M) (b : (⨂[R]^j) M) : a ₜ*b = mulEquiv (a ⊗ₜ b) :=
  rfl

end TensorPower

