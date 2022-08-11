/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Category.Module.Basic

/-!
# Tannaka duality for rings

A ring `R` is equivalent to
the endomorphisms of the additive forgetful functor `Module R ⥤ AddCommGroup`.

-/


universe u

open CategoryTheory

/-- An ingredient of Tannaka duality for rings:
A ring `R` is equivalent to
the endomorphisms of the additive forgetful functor `Module R ⥤ AddCommGroup`.
-/
def ringEquivEndForget₂ (R : Type u) [Ringₓ R] :
    R ≃+* End (AdditiveFunctor.of (forget₂ (ModuleCat.{u} R) AddCommGroupₓₓ.{u})) where
  toFun := fun r =>
    { app := fun M => by
        apply DistribMulAction.toAddMonoidHom M r,
      naturality' := fun M N f => by
        ext
        exact (f.map_smul _ _).symm }
  invFun := fun φ => φ.app (ModuleCat.of R R) (1 : R)
  left_inv := by
    intro r
    simp
  right_inv := by
    intro φ
    ext M x
    simp only [← DistribMulAction.to_add_monoid_hom_apply]
    have w := AddMonoidHom.congr_fun (φ.naturality (ModuleCat.asHomRight (LinearMap.toSpanSingleton R M x))) (1 : R)
    convert w.symm
    exact (one_smul _ _).symm
  map_add' := by
    intros
    ext
    simp [← add_smul]
  map_mul' := by
    intros
    ext
    simpa using mul_smul _ _ _

