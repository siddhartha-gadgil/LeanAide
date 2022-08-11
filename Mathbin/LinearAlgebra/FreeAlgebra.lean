/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.LinearAlgebra.Basis
import Mathbin.Algebra.FreeAlgebra
import Mathbin.LinearAlgebra.FinsuppVectorSpace

/-!
# Linear algebra properties of `free_algebra R X`

This file provides a `free_monoid X` basis on the `free_algebra R X`, and uses it to show the
dimension of the algebra is the cardinality of `list X`
-/


universe u v

namespace FreeAlgebra

/-- The `free_monoid X` basis on the `free_algebra R X`,
mapping `[x₁, x₂, ..., xₙ]` to the "monomial" `1 • x₁ * x₂ * ⋯ * xₙ` -/
@[simps]
noncomputable def basisFreeMonoid (R : Type u) (X : Type v) [CommRingₓ R] : Basis (FreeMonoid X) R (FreeAlgebra R X) :=
  Finsupp.basisSingleOne.map (equivMonoidAlgebraFreeMonoid.symm.toLinearEquiv : _ ≃ₗ[R] FreeAlgebra R X)

-- TODO: generalize to `X : Type v`
theorem dim_eq {K : Type u} {X : Type max u v} [Field K] : Module.rank K (FreeAlgebra K X) = Cardinal.mk (List X) :=
  (Cardinal.lift_inj.mp (basisFreeMonoid K X).mk_eq_dim).symm

end FreeAlgebra

