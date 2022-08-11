/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Topology.Sheaves.SheafCondition.EqualizerProducts
import Mathbin.CategoryTheory.FullSubcategory
import Mathbin.CategoryTheory.Limits.Unit

/-!
# Sheaves

We define sheaves on a topological space, with values in an arbitrary category with products.

The sheaf condition for a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i ⊓ U j)`.

We provide the instance `category (sheaf C X)` as the full subcategory of presheaves,
and the fully faithful functor `sheaf.forget : sheaf C X ⥤ presheaf C X`.

## Equivalent conditions

While the "official" definition is in terms of an equalizer diagram,
in `src/topology/sheaves/sheaf_condition/pairwise_intersections.lean`
and in `src/topology/sheaves/sheaf_condition/open_le_cover.lean`
we provide two equivalent conditions (and prove they are equivalent).

The first is that `F.obj U` is the limit point of the diagram consisting of all the `F.obj (U i)`
and `F.obj (U i ⊓ U j)`.
(That is, we explode the equalizer of two products out into its component pieces.)

The second is that `F.obj U` is the limit point of the diagram constisting of all the `F.obj V`,
for those `V : opens X` such that `V ≤ U i` for some `i`.
(This condition is particularly easy to state, and perhaps should become the "official" definition.)

-/


universe w v u

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

open Opposite

open TopologicalSpace.Opens

namespace Top

variable {C : Type u} [Category.{v} C] [HasProducts.{v} C]

variable {X : Top.{w}} (F : Presheaf C X) {ι : Type v} (U : ι → Opens X)

namespace Presheaf

open SheafConditionEqualizerProducts

/-- The sheaf condition for a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i) ⊓ (U j)`.
-/
def IsSheaf (F : Presheaf.{w, v, u} C X) : Prop :=
  ∀ ⦃ι : Type v⦄ (U : ι → Opens X), Nonempty (IsLimit (SheafConditionEqualizerProducts.fork F U))

/-- The presheaf valued in `unit` over any topological space is a sheaf.
-/
theorem is_sheaf_unit (F : Presheaf (CategoryTheory.Discrete Unit) X) : F.IsSheaf := fun ι U => ⟨punitConeIsLimit⟩

/-- Transfer the sheaf condition across an isomorphism of presheaves.
-/
theorem is_sheaf_of_iso {F G : Presheaf C X} (α : F ≅ G) (h : F.IsSheaf) : G.IsSheaf := fun ι U =>
  ⟨IsLimit.ofIsoLimit ((IsLimit.postcomposeInvEquiv _ _).symm (h U).some)
      (SheafConditionEqualizerProducts.fork.isoOfIso U α.symm).symm⟩

theorem is_sheaf_iso_iff {F G : Presheaf C X} (α : F ≅ G) : F.IsSheaf ↔ G.IsSheaf :=
  ⟨fun h => is_sheaf_of_iso α h, fun h => is_sheaf_of_iso α.symm h⟩

end Presheaf

variable (C X)

/-- A `sheaf C X` is a presheaf of objects from `C` over a (bundled) topological space `X`,
satisfying the sheaf condition.
-/
def Sheaf : Type max u v w :=
  { F : Presheaf C X // F.IsSheaf }deriving Category

-- Let's construct a trivial example, to keep the inhabited linter happy.
instance sheafInhabited : Inhabited (Sheaf (CategoryTheory.Discrete PUnit) X) :=
  ⟨⟨Functor.star _, Presheaf.is_sheaf_unit _⟩⟩

namespace Sheaf

/-- The forgetful functor from sheaves to presheaves.
-/
def forget : Top.Sheaf C X ⥤ Top.Presheaf C X :=
  fullSubcategoryInclusion Presheaf.IsSheaf deriving Full, Faithful

@[simp]
theorem id_app (F : Sheaf C X) (t) : (𝟙 F : F ⟶ F).app t = 𝟙 _ :=
  rfl

@[simp]
theorem comp_app {F G H : Sheaf C X} (f : F ⟶ G) (g : G ⟶ H) (t) : (f ≫ g).app t = f.app t ≫ g.app t :=
  rfl

end Sheaf

end Top

