/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Topology.LocallyConstant.Algebra
import Mathbin.Topology.ContinuousFunction.Basic
import Mathbin.Topology.ContinuousFunction.Algebra

/-!
# The algebra morphism from locally constant functions to continuous functions.

-/


namespace LocallyConstant

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] (f : LocallyConstant X Y)

/-- The inclusion of locally-constant functions into continuous functions as a multiplicative
monoid hom. -/
@[to_additive "The inclusion of locally-constant functions into continuous functions as an\nadditive monoid hom.",
  simps]
def toContinuousMapMonoidHom [Monoidₓ Y] [HasContinuousMul Y] : LocallyConstant X Y →* C(X, Y) where
  toFun := coe
  map_one' := by
    ext
    simp
  map_mul' := fun x y => by
    ext
    simp

/-- The inclusion of locally-constant functions into continuous functions as a linear map. -/
@[simps]
def toContinuousMapLinearMap (R : Type _) [Semiringₓ R] [AddCommMonoidₓ Y] [Module R Y] [HasContinuousAdd Y]
    [HasContinuousConstSmul R Y] : LocallyConstant X Y →ₗ[R] C(X, Y) where
  toFun := coe
  map_add' := fun x y => by
    ext
    simp
  map_smul' := fun x y => by
    ext
    simp

/-- The inclusion of locally-constant functions into continuous functions as an algebra map. -/
@[simps]
def toContinuousMapAlgHom (R : Type _) [CommSemiringₓ R] [Semiringₓ Y] [Algebra R Y] [TopologicalSemiring Y] :
    LocallyConstant X Y →ₐ[R] C(X, Y) where
  toFun := coe
  map_one' := by
    ext
    simp
  map_mul' := fun x y => by
    ext
    simp
  map_zero' := by
    ext
    simp
  map_add' := fun x y => by
    ext
    simp
  commutes' := fun r => by
    ext x
    simp [← Algebra.smul_def]

end LocallyConstant

