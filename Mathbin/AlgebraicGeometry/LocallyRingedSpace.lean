/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.AlgebraicGeometry.RingedSpace
import Mathbin.AlgebraicGeometry.Stalks
import Mathbin.Logic.Equiv.TransferInstance

/-!
# The category of locally ringed spaces

We define (bundled) locally ringed spaces (as `SheafedSpace CommRing` along with the fact that the
stalks are local rings), and morphisms between these (morphisms in `SheafedSpace` with
`is_local_ring_hom` on the stalk maps).
-/


universe v u

open CategoryTheory

open Top

open TopologicalSpace

open Opposite

open CategoryTheory.Category CategoryTheory.Functor

namespace AlgebraicGeometry

/-- A `LocallyRingedSpace` is a topological space equipped with a sheaf of commutative rings
such that all the stalks are local rings.

A morphism of locally ringed spaces is a morphism of ringed spaces
such that the morphisms induced on stalks are local ring homomorphisms. -/
@[nolint has_inhabited_instance]
structure LocallyRingedSpace extends SheafedSpace CommRingₓₓ where
  LocalRing : ∀ x, LocalRing (presheaf.stalk x)

attribute [instance] LocallyRingedSpace.local_ring

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace)

/-- An alias for `to_SheafedSpace`, where the result type is a `RingedSpace`.
This allows us to use dot-notation for the `RingedSpace` namespace.
 -/
def toRingedSpace : RingedSpace :=
  X.toSheafedSpace

/-- The underlying topological space of a locally ringed space. -/
def toTop : Top :=
  X.1.Carrier

instance : CoeSort LocallyRingedSpace (Type u) :=
  ⟨fun X : LocallyRingedSpace => (X.toTop : Type u)⟩

instance (x : X) : LocalRing (X.toPresheafedSpace.stalk x) :=
  X.LocalRing x

/-- The structure sheaf of a locally ringed space. -/
-- PROJECT: how about a typeclass "has_structure_sheaf" to mediate the 𝒪 notation, rather
-- than defining it over and over for PresheafedSpace, LRS, Scheme, etc.
def 𝒪 : Sheaf CommRingₓₓ X.toTop :=
  X.toSheafedSpace.Sheaf

/-- A morphism of locally ringed spaces is a morphism of ringed spaces
 such that the morphims induced on stalks are local ring homomorphisms. -/
def Hom (X Y : LocallyRingedSpace) : Type _ :=
  { f : X.toSheafedSpace ⟶ Y.toSheafedSpace // ∀ x, IsLocalRingHom (PresheafedSpace.stalkMap f x) }

instance : Quiver LocallyRingedSpace :=
  ⟨Hom⟩

@[ext]
theorem hom_ext {X Y : LocallyRingedSpace} (f g : Hom X Y) (w : f.1 = g.1) : f = g :=
  Subtype.eq w

/-- The stalk of a locally ringed space, just as a `CommRing`.
-/
-- TODO perhaps we should make a bundled `LocalRing` and return one here?
-- TODO define `sheaf.stalk` so we can write `X.𝒪.stalk` here?
noncomputable def stalk (X : LocallyRingedSpace) (x : X) : CommRingₓₓ :=
  X.Presheaf.stalk x

/-- A morphism of locally ringed spaces `f : X ⟶ Y` induces
a local ring homomorphism from `Y.stalk (f x)` to `X.stalk x` for any `x : X`.
-/
noncomputable def stalkMap {X Y : LocallyRingedSpace} (f : X ⟶ Y) (x : X) : Y.stalk (f.1.1 x) ⟶ X.stalk x :=
  PresheafedSpace.stalkMap f.1 x

instance {X Y : LocallyRingedSpace} (f : X ⟶ Y) (x : X) : IsLocalRingHom (stalkMap f x) :=
  f.2 x

instance {X Y : LocallyRingedSpace} (f : X ⟶ Y) (x : X) : IsLocalRingHom (PresheafedSpace.stalkMap f.1 x) :=
  f.2 x

/-- The identity morphism on a locally ringed space. -/
@[simps]
def id (X : LocallyRingedSpace) : Hom X X :=
  ⟨𝟙 _, fun x => by
    erw [PresheafedSpace.stalk_map.id]
    apply is_local_ring_hom_id⟩

instance (X : LocallyRingedSpace) : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms of locally ringed spaces. -/
@[simps]
def comp {X Y Z : LocallyRingedSpace} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  ⟨f.val ≫ g.val, fun x => by
    erw [PresheafedSpace.stalk_map.comp]
    exact @is_local_ring_hom_comp _ _ _ _ _ _ _ _ (f.2 _) (g.2 _)⟩

/-- The category of locally ringed spaces. -/
instance : Category LocallyRingedSpace where
  Hom := Hom
  id := id
  comp := fun X Y Z f g => comp f g
  comp_id' := by
    intros
    ext1
    simp
  id_comp' := by
    intros
    ext1
    simp
  assoc' := by
    intros
    ext1
    simp

/-- The forgetful functor from `LocallyRingedSpace` to `SheafedSpace CommRing`. -/
@[simps]
def forgetToSheafedSpace : LocallyRingedSpace ⥤ SheafedSpace CommRingₓₓ where
  obj := fun X => X.toSheafedSpace
  map := fun X Y f => f.1

instance : Faithful forgetToSheafedSpace where

/-- The forgetful functor from `LocallyRingedSpace` to `Top`. -/
@[simps]
def forgetToTop : LocallyRingedSpace ⥤ Top :=
  forget_to_SheafedSpace ⋙ SheafedSpace.forget _

@[simp]
theorem comp_val {X Y Z : LocallyRingedSpace} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).val = f.val ≫ g.val :=
  rfl

@[simp]
theorem comp_val_c {X Y Z : LocallyRingedSpace} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val.c = g.val.c ≫ (Presheaf.pushforward _ g.val.base).map f.val.c :=
  rfl

theorem comp_val_c_app {X Y Z : LocallyRingedSpace} (f : X ⟶ Y) (g : Y ⟶ Z) (U : (Opens Z)ᵒᵖ) :
    (f ≫ g).val.c.app U = g.val.c.app U ≫ f.val.c.app (op <| (Opens.map g.val.base).obj U.unop) :=
  rfl

/-- Given two locally ringed spaces `X` and `Y`, an isomorphism between `X` and `Y` as _sheafed_
spaces can be lifted to a morphism `X ⟶ Y` as locally ringed spaces.

See also `iso_of_SheafedSpace_iso`.
-/
@[simps]
def homOfSheafedSpaceHomOfIsIso {X Y : LocallyRingedSpace} (f : X.toSheafedSpace ⟶ Y.toSheafedSpace) [IsIso f] :
    X ⟶ Y :=
  (Subtype.mk f) fun x =>
    -- Here we need to see that the stalk maps are really local ring homomorphisms.
    -- This can be solved by type class inference, because stalk maps of isomorphisms are isomorphisms
    -- and isomorphisms are local ring homomorphisms.
    show IsLocalRingHom (PresheafedSpace.stalkMap (SheafedSpace.forgetToPresheafedSpace.map f) x) by
      infer_instance

/-- Given two locally ringed spaces `X` and `Y`, an isomorphism between `X` and `Y` as _sheafed_
spaces can be lifted to an isomorphism `X ⟶ Y` as locally ringed spaces.

This is related to the property that the functor `forget_to_SheafedSpace` reflects isomorphisms.
In fact, it is slightly stronger as we do not require `f` to come from a morphism between
_locally_ ringed spaces.
-/
def isoOfSheafedSpaceIso {X Y : LocallyRingedSpace} (f : X.toSheafedSpace ≅ Y.toSheafedSpace) : X ≅ Y where
  Hom := homOfSheafedSpaceHomOfIsIso f.Hom
  inv := homOfSheafedSpaceHomOfIsIso f.inv
  hom_inv_id' := hom_ext _ _ f.hom_inv_id
  inv_hom_id' := hom_ext _ _ f.inv_hom_id

instance :
    ReflectsIsomorphisms
      forgetToSheafedSpace where reflects := fun X Y f i =>
    { out :=
        ⟨hom_of_SheafedSpace_hom_of_is_iso (CategoryTheory.inv (forget_to_SheafedSpace.map f)),
          hom_ext _ _ (is_iso.hom_inv_id _), hom_ext _ _ (is_iso.inv_hom_id _)⟩ }

instance is_SheafedSpace_iso {X Y : LocallyRingedSpace} (f : X ⟶ Y) [IsIso f] : IsIso f.1 :=
  LocallyRingedSpace.forgetToSheafedSpace.map_is_iso f

/-- The restriction of a locally ringed space along an open embedding.
-/
@[simps]
def restrict {U : Top} (X : LocallyRingedSpace) {f : U ⟶ X.toTop} (h : OpenEmbedding f) : LocallyRingedSpace where
  LocalRing := by
    intro x
    dsimp'  at *
    -- We show that the stalk of the restriction is isomorphic to the original stalk,
    apply @RingEquiv.local_ring _ _ _ (X.local_ring (f x))
    exact (X.to_PresheafedSpace.restrict_stalk_iso h x).symm.commRingIsoToRingEquiv
  toSheafedSpace := X.toSheafedSpace.restrict h

/-- The canonical map from the restriction to the supspace. -/
def ofRestrict {U : Top} (X : LocallyRingedSpace) {f : U ⟶ X.toTop} (h : OpenEmbedding f) : X.restrict h ⟶ X :=
  ⟨X.toPresheafedSpace.ofRestrict h, fun x => inferInstance⟩

/-- The restriction of a locally ringed space `X` to the top subspace is isomorphic to `X` itself.
-/
def restrictTopIso (X : LocallyRingedSpace) : X.restrict (Opens.open_embedding ⊤) ≅ X :=
  @isoOfSheafedSpaceIso (X.restrict (Opens.open_embedding ⊤)) X X.toSheafedSpace.restrictTopIso

/-- The global sections, notated Gamma.
-/
def Γ : LocallyRingedSpaceᵒᵖ ⥤ CommRingₓₓ :=
  forgetToSheafedSpace.op ⋙ SheafedSpace.Γ

theorem Γ_def : Γ = forgetToSheafedSpace.op ⋙ SheafedSpace.Γ :=
  rfl

@[simp]
theorem Γ_obj (X : LocallyRingedSpaceᵒᵖ) : Γ.obj X = (unop X).Presheaf.obj (op ⊤) :=
  rfl

theorem Γ_obj_op (X : LocallyRingedSpace) : Γ.obj (op X) = X.Presheaf.obj (op ⊤) :=
  rfl

@[simp]
theorem Γ_map {X Y : LocallyRingedSpaceᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.1.c.app (op ⊤) :=
  rfl

theorem Γ_map_op {X Y : LocallyRingedSpace} (f : X ⟶ Y) : Γ.map f.op = f.1.c.app (op ⊤) :=
  rfl

theorem preimage_basic_open {X Y : LocallyRingedSpace} (f : X ⟶ Y) {U : Opens Y} (s : Y.Presheaf.obj (op U)) :
    (Opens.map f.1.base).obj (Y.toRingedSpace.basicOpen s) =
      @RingedSpace.basicOpen X.toRingedSpace ((Opens.map f.1.base).obj U) (f.1.c.app _ s) :=
  by
  ext
  constructor
  · rintro ⟨⟨y, hyU⟩, hy : IsUnit _, rfl : y = _⟩
    erw [RingedSpace.mem_basic_open _ _ ⟨x, show x ∈ (opens.map f.1.base).obj U from hyU⟩]
    rw [← PresheafedSpace.stalk_map_germ_apply]
    exact (PresheafedSpace.stalk_map f.1 _).is_unit_map hy
    
  · rintro ⟨y, hy : IsUnit _, rfl⟩
    erw [RingedSpace.mem_basic_open _ _ ⟨f.1.base y.1, y.2⟩]
    rw [← PresheafedSpace.stalk_map_germ_apply] at hy
    exact (is_unit_map_iff (PresheafedSpace.stalk_map f.1 _) _).mp hy
    

-- This actually holds for all ringed spaces with nontrivial stalks.
@[simp]
theorem basic_open_zero (X : LocallyRingedSpace) (U : Opens X.Carrier) :
    X.toRingedSpace.basicOpen (0 : X.Presheaf.obj <| op U) = ∅ := by
  ext
  simp only [← Set.mem_empty_eq, ← TopologicalSpace.Opens.empty_eq, ← TopologicalSpace.Opens.mem_coe, ← opens.coe_bot, ←
    iff_falseₓ, ← RingedSpace.basic_open, ← is_unit_zero_iff, ← Set.mem_set_of_eq, ← map_zero]
  rintro ⟨⟨y, _⟩, h, e⟩
  exact @zero_ne_one (X.presheaf.stalk y) _ _ h

instance component_nontrivial (X : LocallyRingedSpace) (U : Opens X.Carrier) [hU : Nonempty U] :
    Nontrivial (X.Presheaf.obj <| op U) :=
  (X.toPresheafedSpace.Presheaf.germ hU.some).domain_nontrivial

end LocallyRingedSpace

end AlgebraicGeometry

