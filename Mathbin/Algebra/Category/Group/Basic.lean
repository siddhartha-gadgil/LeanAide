/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Algebra.Category.Mon.Basic
import Mathbin.CategoryTheory.Endomorphism

/-!
# Category instances for group, add_group, comm_group, and add_comm_group.

We introduce the bundled categories:
* `Group`
* `AddGroup`
* `CommGroup`
* `AddCommGroup`
along with the relevant forgetful functors between them, and to the bundled monoid categories.
-/


universe u v

open CategoryTheory

/-- The category of groups and group morphisms. -/
@[to_additive AddGroupₓₓ]
def Groupₓₓ : Type (u + 1) :=
  Bundled Groupₓ

/-- The category of additive groups and group morphisms -/
add_decl_doc AddGroupₓₓ

namespace Groupₓₓ

@[to_additive]
instance : BundledHom.ParentProjection Groupₓ.toMonoid :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for Groupₓₓ

attribute [to_additive] Groupₓₓ.largeCategory Groupₓₓ.concreteCategory

@[to_additive]
instance : CoeSort Groupₓₓ (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled `Group` from the underlying type and typeclass. -/
@[to_additive]
def of (X : Type u) [Groupₓ X] : Groupₓₓ :=
  Bundled.of X

/-- Construct a bundled `AddGroup` from the underlying type and typeclass. -/
add_decl_doc AddGroupₓₓ.of

/-- Typecheck a `monoid_hom` as a morphism in `Group`. -/
@[to_additive]
def ofHom {X Y : Type u} [Groupₓ X] [Groupₓ Y] (f : X →* Y) : of X ⟶ of Y :=
  f

/-- Typecheck a `add_monoid_hom` as a morphism in `AddGroup`. -/
add_decl_doc AddGroupₓₓ.ofHom

@[simp, to_additive]
theorem of_hom_apply {X Y : Type _} [Groupₓ X] [Groupₓ Y] (f : X →* Y) (x : X) : ofHom f x = f x :=
  rfl

@[to_additive]
instance (G : Groupₓₓ) : Groupₓ G :=
  G.str

@[simp, to_additive]
theorem coe_of (R : Type u) [Groupₓ R] : (Groupₓₓ.of R : Type u) = R :=
  rfl

@[to_additive]
instance : Inhabited Groupₓₓ :=
  ⟨Groupₓₓ.of PUnit⟩

@[to_additive]
instance ofUnique (G : Type _) [Groupₓ G] [i : Unique G] : Unique (Groupₓₓ.of G) :=
  i

@[simp, to_additive]
theorem one_apply (G H : Groupₓₓ) (g : G) : (1 : G ⟶ H) g = 1 :=
  rfl

@[ext, to_additive]
theorem ext (G H : Groupₓₓ) (f₁ f₂ : G ⟶ H) (w : ∀ x, f₁ x = f₂ x) : f₁ = f₂ := by
  ext1
  apply w

@[to_additive has_forget_to_AddMon]
instance hasForgetToMon : HasForget₂ Groupₓₓ Mon :=
  BundledHom.forget₂ _ _

@[to_additive]
instance : Coe Groupₓₓ.{u} Mon.{u} where coe := (forget₂ Groupₓₓ Mon).obj

end Groupₓₓ

/-- The category of commutative groups and group morphisms. -/
@[to_additive AddCommGroupₓₓ]
def CommGroupₓₓ : Type (u + 1) :=
  Bundled CommGroupₓ

/-- The category of additive commutative groups and group morphisms. -/
add_decl_doc AddCommGroupₓₓ

/-- `Ab` is an abbreviation for `AddCommGroup`, for the sake of mathematicians' sanity. -/
abbrev Ab :=
  AddCommGroupₓₓ

namespace CommGroupₓₓ

@[to_additive]
instance : BundledHom.ParentProjection CommGroupₓ.toGroup :=
  ⟨⟩

deriving instance LargeCategory, ConcreteCategory for CommGroupₓₓ

attribute [to_additive] CommGroupₓₓ.largeCategory CommGroupₓₓ.concreteCategory

@[to_additive]
instance : CoeSort CommGroupₓₓ (Type _) :=
  bundled.has_coe_to_sort

/-- Construct a bundled `CommGroup` from the underlying type and typeclass. -/
@[to_additive]
def of (G : Type u) [CommGroupₓ G] : CommGroupₓₓ :=
  Bundled.of G

/-- Construct a bundled `AddCommGroup` from the underlying type and typeclass. -/
add_decl_doc AddCommGroupₓₓ.of

/-- Typecheck a `monoid_hom` as a morphism in `CommGroup`. -/
@[to_additive]
def ofHom {X Y : Type u} [CommGroupₓ X] [CommGroupₓ Y] (f : X →* Y) : of X ⟶ of Y :=
  f

/-- Typecheck a `add_monoid_hom` as a morphism in `AddCommGroup`. -/
add_decl_doc AddCommGroupₓₓ.ofHom

@[simp, to_additive]
theorem of_hom_apply {X Y : Type _} [CommGroupₓ X] [CommGroupₓ Y] (f : X →* Y) (x : X) : ofHom f x = f x :=
  rfl

@[to_additive]
instance commGroupInstance (G : CommGroupₓₓ) : CommGroupₓ G :=
  G.str

@[simp, to_additive]
theorem coe_of (R : Type u) [CommGroupₓ R] : (CommGroupₓₓ.of R : Type u) = R :=
  rfl

@[to_additive]
instance : Inhabited CommGroupₓₓ :=
  ⟨CommGroupₓₓ.of PUnit⟩

@[to_additive]
instance ofUnique (G : Type _) [CommGroupₓ G] [i : Unique G] : Unique (CommGroupₓₓ.of G) :=
  i

@[simp, to_additive]
theorem one_apply (G H : CommGroupₓₓ) (g : G) : (1 : G ⟶ H) g = 1 :=
  rfl

@[ext, to_additive]
theorem ext (G H : CommGroupₓₓ) (f₁ f₂ : G ⟶ H) (w : ∀ x, f₁ x = f₂ x) : f₁ = f₂ := by
  ext1
  apply w

@[to_additive has_forget_to_AddGroup]
instance hasForgetToGroup : HasForget₂ CommGroupₓₓ Groupₓₓ :=
  BundledHom.forget₂ _ _

@[to_additive]
instance : Coe CommGroupₓₓ.{u} Groupₓₓ.{u} where coe := (forget₂ CommGroupₓₓ Groupₓₓ).obj

@[to_additive has_forget_to_AddCommMon]
instance hasForgetToCommMon : HasForget₂ CommGroupₓₓ CommMon :=
  InducedCategory.hasForget₂ fun G : CommGroupₓₓ => CommMon.of G

@[to_additive]
instance : Coe CommGroupₓₓ.{u} CommMon.{u} where coe := (forget₂ CommGroupₓₓ CommMon).obj

end CommGroupₓₓ

-- This example verifies an improvement possible in Lean 3.8.
-- Before that, to have `monoid_hom.map_map` usable by `simp` here,
-- we had to mark all the concrete category `has_coe_to_sort` instances reducible.
-- Now, it just works.
@[to_additive]
example {R S : CommGroupₓₓ} (i : R ⟶ S) (r : R) (h : r = 1) : i r = 1 := by
  simp [← h]

namespace AddCommGroupₓₓ

/-- Any element of an abelian group gives a unique morphism from `ℤ` sending
`1` to that element. -/
-- Note that because `ℤ : Type 0`, this forces `G : AddCommGroup.{0}`,
-- so we write this explicitly to be clear.
-- TODO generalize this, requiring a `ulift_instances.lean` file
def asHom {G : AddCommGroupₓₓ.{0}} (g : G) : AddCommGroupₓₓ.of ℤ ⟶ G :=
  zmultiplesHom G g

@[simp]
theorem as_hom_apply {G : AddCommGroupₓₓ.{0}} (g : G) (i : ℤ) : (asHom g) i = i • g :=
  rfl

theorem as_hom_injective {G : AddCommGroupₓₓ.{0}} : Function.Injective (@asHom G) := fun h k w => by
  convert congr_arg (fun k : AddCommGroupₓₓ.of ℤ ⟶ G => (k : ℤ → G) (1 : ℤ)) w <;> simp

@[ext]
theorem int_hom_ext {G : AddCommGroupₓₓ.{0}} (f g : AddCommGroupₓₓ.of ℤ ⟶ G) (w : f (1 : ℤ) = g (1 : ℤ)) : f = g :=
  AddMonoidHom.ext_int w

-- TODO: this argument should be generalised to the situation where
-- the forgetful functor is representable.
theorem injective_of_mono {G H : AddCommGroupₓₓ.{0}} (f : G ⟶ H) [Mono f] : Function.Injective f := fun g₁ g₂ h => by
  have t0 : as_hom g₁ ≫ f = as_hom g₂ ≫ f := by
    ext
    simpa [← as_hom_apply] using h
  have t1 : as_hom g₁ = as_hom g₂ := (cancel_mono _).1 t0
  apply as_hom_injective t1

end AddCommGroupₓₓ

/-- Build an isomorphism in the category `Group` from a `mul_equiv` between `group`s. -/
@[to_additive AddEquiv.toAddGroupIso, simps]
def MulEquiv.toGroupIso {X Y : Groupₓₓ} (e : X ≃* Y) : X ≅ Y where
  Hom := e.toMonoidHom
  inv := e.symm.toMonoidHom

/-- Build an isomorphism in the category `AddGroup` from an `add_equiv` between `add_group`s. -/
add_decl_doc AddEquiv.toAddGroupIso

/-- Build an isomorphism in the category `CommGroup` from a `mul_equiv` between `comm_group`s. -/
@[to_additive AddEquiv.toAddCommGroupIso, simps]
def MulEquiv.toCommGroupIso {X Y : CommGroupₓₓ} (e : X ≃* Y) : X ≅ Y where
  Hom := e.toMonoidHom
  inv := e.symm.toMonoidHom

/-- Build an isomorphism in the category `AddCommGroup` from a `add_equiv` between
`add_comm_group`s. -/
add_decl_doc AddEquiv.toAddCommGroupIso

namespace CategoryTheory.Iso

/-- Build a `mul_equiv` from an isomorphism in the category `Group`. -/
@[to_additive AddGroup_iso_to_add_equiv "Build an `add_equiv` from an isomorphism in the category\n`AddGroup`.", simps]
def groupIsoToMulEquiv {X Y : Groupₓₓ} (i : X ≅ Y) : X ≃* Y :=
  i.Hom.toMulEquiv i.inv i.hom_inv_id i.inv_hom_id

/-- Build a `mul_equiv` from an isomorphism in the category `CommGroup`. -/
@[to_additive AddCommGroup_iso_to_add_equiv "Build an `add_equiv` from an isomorphism\nin the category `AddCommGroup`.",
  simps]
def commGroupIsoToMulEquiv {X Y : CommGroupₓₓ} (i : X ≅ Y) : X ≃* Y :=
  i.Hom.toMulEquiv i.inv i.hom_inv_id i.inv_hom_id

end CategoryTheory.Iso

/-- multiplicative equivalences between `group`s are the same as (isomorphic to) isomorphisms
in `Group` -/
@[to_additive addEquivIsoAddGroupIso
      "additive equivalences between `add_group`s are the same\nas (isomorphic to) isomorphisms in `AddGroup`"]
def mulEquivIsoGroupIso {X Y : Groupₓₓ.{u}} : X ≃* Y ≅ X ≅ Y where
  Hom := fun e => e.toGroupIso
  inv := fun i => i.groupIsoToMulEquiv

/-- multiplicative equivalences between `comm_group`s are the same as (isomorphic to) isomorphisms
in `CommGroup` -/
@[to_additive addEquivIsoAddCommGroupIso
      "additive equivalences between `add_comm_group`s are\nthe same as (isomorphic to) isomorphisms in `AddCommGroup`"]
def mulEquivIsoCommGroupIso {X Y : CommGroupₓₓ.{u}} : X ≃* Y ≅ X ≅ Y where
  Hom := fun e => e.toCommGroupIso
  inv := fun i => i.commGroupIsoToMulEquiv

namespace CategoryTheory.Aut

/-- The (bundled) group of automorphisms of a type is isomorphic to the (bundled) group
of permutations. -/
def isoPerm {α : Type u} : Groupₓₓ.of (Aut α) ≅ Groupₓₓ.of (Equivₓ.Perm α) where
  Hom :=
    ⟨fun g => g.toEquiv, by
      tidy, by
      tidy⟩
  inv :=
    ⟨fun g => g.toIso, by
      tidy, by
      tidy⟩

/-- The (unbundled) group of automorphisms of a type is `mul_equiv` to the (unbundled) group
of permutations. -/
def mulEquivPerm {α : Type u} : Aut α ≃* Equivₓ.Perm α :=
  isoPerm.groupIsoToMulEquiv

end CategoryTheory.Aut

@[to_additive]
instance Groupₓₓ.forget_reflects_isos :
    ReflectsIsomorphisms (forget Groupₓₓ.{u}) where reflects := fun X Y f _ => by
    skip
    let i := as_iso ((forget Groupₓₓ).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_Group_iso).1⟩

@[to_additive]
instance CommGroupₓₓ.forget_reflects_isos :
    ReflectsIsomorphisms (forget CommGroupₓₓ.{u}) where reflects := fun X Y f _ => by
    skip
    let i := as_iso ((forget CommGroupₓₓ).map f)
    let e : X ≃* Y := { f, i.to_equiv with }
    exact ⟨(is_iso.of_iso e.to_CommGroup_iso).1⟩

