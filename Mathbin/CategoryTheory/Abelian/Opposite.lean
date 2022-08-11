/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Abelian.Basic
import Mathbin.CategoryTheory.Preadditive.Opposite
import Mathbin.CategoryTheory.Limits.Opposites
import Mathbin.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# The opposite of an abelian category is abelian.
-/


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

variable (C : Type _) [Category C] [Abelian C]

attribute [local instance]
  finite_limits_from_equalizers_and_finite_products finite_colimits_from_coequalizers_and_finite_coproducts has_finite_limits_opposite has_finite_colimits_opposite has_finite_products_opposite

instance : Abelian Cᵒᵖ where
  normalMonoOfMono := fun X Y f m => normal_mono_of_normal_epi_unop _ (normal_epi_of_epi f.unop)
  normalEpiOfEpi := fun X Y f m => normal_epi_of_normal_mono_unop _ (normal_mono_of_mono f.unop)

section

variable {C} {X Y : C} (f : X ⟶ Y) {A B : Cᵒᵖ} (g : A ⟶ B)

/-- The kernel of `f.op` is the opposite of `cokernel f`. -/
-- TODO: Generalize (this will work whenever f has a cokernel)
-- (The abelian case is probably sufficient for most applications.)
@[simps]
def kernelOpUnop : (kernel f.op).unop ≅ cokernel f where
  Hom :=
    (kernel.lift f.op (cokernel.π f).op <| by
        simp [op_comp]).unop
  inv :=
    cokernel.desc f (kernel.ι f.op).unop <| by
      rw [← f.unop_op, ← unop_comp, f.unop_op]
      simp
  hom_inv_id' := by
    rw [← unop_id, ← (cokernel.desc f _ _).unop_op, ← unop_comp]
    congr 1
    dsimp'
    ext
    simp [op_comp]
  inv_hom_id' := by
    dsimp'
    ext
    simp [unop_comp]

/-- The cokernel of `f.op` is the opposite of `kernel f`. -/
-- TODO: Generalize (this will work whenever f has a kernel)
-- (The abelian case is probably sufficient for most applications.)
@[simps]
def cokernelOpUnop : (cokernel f.op).unop ≅ kernel f where
  Hom :=
    kernel.lift f (cokernel.π f.op).unop <| by
      rw [← f.unop_op, ← unop_comp, f.unop_op]
      simp
  inv :=
    (cokernel.desc f.op (kernel.ι f).op <| by
        simp [op_comp]).unop
  hom_inv_id' := by
    rw [← unop_id, ← (kernel.lift f _ _).unop_op, ← unop_comp]
    congr 1
    dsimp'
    ext
    simp [op_comp]
  inv_hom_id' := by
    dsimp'
    ext
    simp [unop_comp]

/-- The kernel of `g.unop` is the opposite of `cokernel g`. -/
@[simps]
def kernelUnopOp : Opposite.op (kernel g.unop) ≅ cokernel g :=
  (cokernelOpUnop g.unop).op

/-- The cokernel of `g.unop` is the opposite of `kernel g`. -/
@[simps]
def cokernelUnopOp : Opposite.op (cokernel g.unop) ≅ kernel g :=
  (kernelOpUnop g.unop).op

theorem Cokernel.π_op :
    (cokernel.π f.op).unop = (cokernelOpUnop f).Hom ≫ kernel.ι f ≫ eqToHom (Opposite.unop_op _).symm := by
  simp [← cokernel_op_unop]

theorem Kernel.ι_op : (kernel.ι f.op).unop = eqToHom (Opposite.unop_op _) ≫ cokernel.π f ≫ (kernelOpUnop f).inv := by
  simp [← kernel_op_unop]

/-- The kernel of `f.op` is the opposite of `cokernel f`. -/
@[simps]
def kernelOpOp : kernel f.op ≅ Opposite.op (cokernel f) :=
  (kernelOpUnop f).op.symm

/-- The cokernel of `f.op` is the opposite of `kernel f`. -/
@[simps]
def cokernelOpOp : cokernel f.op ≅ Opposite.op (kernel f) :=
  (cokernelOpUnop f).op.symm

/-- The kernel of `g.unop` is the opposite of `cokernel g`. -/
@[simps]
def kernelUnopUnop : kernel g.unop ≅ (cokernel g).unop :=
  (kernelUnopOp g).unop.symm

theorem Kernel.ι_unop : (kernel.ι g.unop).op = eqToHom (Opposite.op_unop _) ≫ cokernel.π g ≫ (kernelUnopOp g).inv := by
  simp

theorem Cokernel.π_unop :
    (cokernel.π g.unop).op = (cokernelUnopOp g).Hom ≫ kernel.ι g ≫ eqToHom (Opposite.op_unop _).symm := by
  simp

/-- The cokernel of `g.unop` is the opposite of `kernel g`. -/
@[simps]
def cokernelUnopUnop : cokernel g.unop ≅ (kernel g).unop :=
  (cokernelUnopOp g).unop.symm

end

end CategoryTheory

