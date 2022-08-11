/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Adam Topaz
-/
import Mathbin.CategoryTheory.ConcreteCategory.Basic
import Mathbin.CategoryTheory.FullSubcategory
import Mathbin.CategoryTheory.Skeletal
import Mathbin.CategoryTheory.Elementwise
import Mathbin.Data.Fin.Basic
import Mathbin.Data.Fintype.Basic

/-!
# The category of finite types.

We define the category of finite types, denoted `Fintype` as
(bundled) types with a `fintype` instance.

We also define `Fintype.skeleton`, the standard skeleton of `Fintype` whose objects are `fin n`
for `n : ℕ`. We prove that the obvious inclusion functor `Fintype.skeleton ⥤ Fintype` is an
equivalence of categories in `Fintype.skeleton.equivalence`.
We prove that `Fintype.skeleton` is a skeleton of `Fintype` in `Fintype.is_skeleton`.
-/


open Classical

open CategoryTheory

/-- The category of finite types. -/
def Fintypeₓ :=
  Bundled Fintype

namespace Fintypeₓ

instance : CoeSort Fintypeₓ (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled `Fintype` from the underlying type and typeclass. -/
def of (X : Type _) [Fintype X] : Fintypeₓ :=
  Bundled.of X

instance : Inhabited Fintypeₓ :=
  ⟨⟨Pempty⟩⟩

instance {X : Fintypeₓ} : Fintype X :=
  X.2

instance : Category Fintypeₓ :=
  InducedCategory.category Bundled.α

/-- The fully faithful embedding of `Fintype` into the category of types. -/
@[simps]
def incl : Fintypeₓ ⥤ Type _ :=
  inducedFunctor _ deriving Full, Faithful

instance concreteCategoryFintype : ConcreteCategory Fintypeₓ :=
  ⟨incl⟩

@[simp]
theorem id_apply (X : Fintypeₓ) (x : X) : (𝟙 X : X → X) x = x :=
  rfl

@[simp]
theorem comp_apply {X Y Z : Fintypeₓ} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) :=
  rfl

/-- Equivalences between finite types are the same as isomorphisms in `Fintype`. -/
-- See `equiv_equiv_iso` in the root namespace for the analogue in `Type`.
@[simps]
def equivEquivIso {A B : Fintypeₓ} : A ≃ B ≃ (A ≅ B) where
  toFun := fun e => { Hom := e, inv := e.symm }
  invFun := fun i =>
    { toFun := i.Hom, invFun := i.inv, left_inv := Iso.hom_inv_id_apply i, right_inv := Iso.inv_hom_id_apply i }
  left_inv := by
    tidy
  right_inv := by
    tidy

universe u

/-- The "standard" skeleton for `Fintype`. This is the full subcategory of `Fintype` spanned by objects
of the form `ulift (fin n)` for `n : ℕ`. We parameterize the objects of `Fintype.skeleton`
directly as `ulift ℕ`, as the type `ulift (fin m) ≃ ulift (fin n)` is
nonempty if and only if `n = m`. Specifying universes, `skeleton : Type u` is a small
skeletal category equivalent to `Fintype.{u}`.
-/
def Skeleton : Type u :=
  ULift ℕ

namespace Skeleton

/-- Given any natural number `n`, this creates the associated object of `Fintype.skeleton`. -/
def mk : ℕ → Skeleton :=
  ULift.up

instance : Inhabited Skeleton :=
  ⟨mk 0⟩

/-- Given any object of `Fintype.skeleton`, this returns the associated natural number. -/
def len : Skeleton → ℕ :=
  ULift.down

@[ext]
theorem ext (X Y : Skeleton) : X.len = Y.len → X = Y :=
  ULift.ext _ _

instance : SmallCategory Skeleton.{u} where
  Hom := fun X Y => ULift.{u} (Finₓ X.len) → ULift.{u} (Finₓ Y.len)
  id := fun _ => id
  comp := fun _ _ _ f g => g ∘ f

theorem is_skeletal : Skeletal Skeleton.{u} := fun X Y ⟨h⟩ =>
  ext _ _ <|
    Finₓ.equiv_iff_eq.mp <|
      Nonempty.intro <|
        { toFun := fun x => (h.Hom ⟨x⟩).down, invFun := fun x => (h.inv ⟨x⟩).down,
          left_inv := by
            intro a
            change ULift.down _ = _
            rw [ULift.up_down]
            change ((h.hom ≫ h.inv) _).down = _
            simpa,
          right_inv := by
            intro a
            change ULift.down _ = _
            rw [ULift.up_down]
            change ((h.inv ≫ h.hom) _).down = _
            simpa }

/-- The canonical fully faithful embedding of `Fintype.skeleton` into `Fintype`. -/
def incl : skeleton.{u} ⥤ Fintypeₓ.{u} where
  obj := fun X => Fintypeₓ.of (ULift (Finₓ X.len))
  map := fun _ _ f => f

instance : Full incl where preimage := fun _ _ f => f

instance : Faithful incl where

instance : EssSurj incl :=
  ess_surj.mk fun X =>
    let F := Fintype.equivFin X
    ⟨mk (Fintype.card X), Nonempty.intro { Hom := F.symm ∘ ULift.down, inv := ULift.up ∘ F }⟩

noncomputable instance : IsEquivalence incl :=
  Equivalence.ofFullyFaithfullyEssSurj _

/-- The equivalence between `Fintype.skeleton` and `Fintype`. -/
noncomputable def equivalence : skeleton ≌ Fintypeₓ :=
  incl.asEquivalence

@[simp]
theorem incl_mk_nat_card (n : ℕ) : Fintype.card (incl.obj (mk n)) = n := by
  convert Finset.card_fin n
  apply Fintype.of_equiv_card

end Skeleton

/-- `Fintype.skeleton` is a skeleton of `Fintype`. -/
noncomputable def isSkeleton : IsSkeletonOf Fintypeₓ Skeleton Skeleton.incl where
  skel := Skeleton.is_skeletal
  eqv := by
    infer_instance

end Fintypeₓ

