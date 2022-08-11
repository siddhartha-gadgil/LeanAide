/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom
import Mathbin.Topology.Bornology.Hom

/-!
# The category of bornologies

This defines `Born`, the category of bornologies.
-/


universe u

open CategoryTheory

/-- The category of bornologies. -/
def Born :=
  Bundled Bornology

namespace Born

instance : CoeSort Born (Type _) :=
  bundled.has_coe_to_sort

instance (X : Born) : Bornology X :=
  X.str

/-- Construct a bundled `Born` from a `bornology`. -/
def of (α : Type _) [Bornology α] : Born :=
  Bundled.of α

instance : Inhabited Born :=
  ⟨of PUnit⟩

instance : BundledHom @LocallyBoundedMap where
  toFun := fun _ _ _ _ => coeFn
  id := @LocallyBoundedMap.id
  comp := @LocallyBoundedMap.comp
  hom_ext := fun X Y _ _ => FunLike.coe_injective

instance : LargeCategory.{u} Born :=
  BundledHom.category LocallyBoundedMap

instance : ConcreteCategory Born :=
  BundledHom.concreteCategory LocallyBoundedMap

end Born

