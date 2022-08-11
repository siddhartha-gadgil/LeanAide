/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.Algebra.Category.Group.ZModuleEquivalence
import Mathbin.Algebra.Category.Group.Limits
import Mathbin.Algebra.Category.Group.Colimits
import Mathbin.Algebra.Category.Module.Abelian
import Mathbin.CategoryTheory.Abelian.Basic

/-!
# The category of abelian groups is abelian
-/


open CategoryTheory

open CategoryTheory.Limits

universe u

noncomputable section

namespace AddCommGroupₓₓ

section

variable {X Y : AddCommGroupₓₓ.{u}} (f : X ⟶ Y)

/-- In the category of abelian groups, every monomorphism is normal. -/
def normalMono (hf : Mono f) : NormalMono f :=
  equivalenceReflectsNormalMono (forget₂ (ModuleCat.{u} ℤ) AddCommGroupₓₓ.{u}).inv <|
    ModuleCat.normalMono _ inferInstance

/-- In the category of abelian groups, every epimorphism is normal. -/
def normalEpi (hf : Epi f) : NormalEpi f :=
  equivalenceReflectsNormalEpi (forget₂ (ModuleCat.{u} ℤ) AddCommGroupₓₓ.{u}).inv <| ModuleCat.normalEpi _ inferInstance

end

/-- The category of abelian groups is abelian. -/
instance : Abelian AddCommGroupₓₓ.{u} where
  HasFiniteProducts :=
    ⟨by
      infer_instance⟩
  normalMonoOfMono := fun X Y => normalMono
  normalEpiOfEpi := fun X Y => normalEpi
  add_comp' := by
    intros
    simp only [← preadditive.add_comp]
  comp_add' := by
    intros
    simp only [← preadditive.comp_add]

end AddCommGroupₓₓ

