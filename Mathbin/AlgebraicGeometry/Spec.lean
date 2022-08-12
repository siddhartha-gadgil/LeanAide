/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Justus Springer
-/
import Mathbin.AlgebraicGeometry.LocallyRingedSpace
import Mathbin.AlgebraicGeometry.StructureSheaf
import Mathbin.Logic.Equiv.TransferInstance
import Mathbin.RingTheory.Localization.LocalizationLocalization
import Mathbin.Topology.Sheaves.SheafCondition.Sites
import Mathbin.Topology.Sheaves.Functors

/-!
# $Spec$ as a functor to locally ringed spaces.

We define the functor $Spec$ from commutative rings to locally ringed spaces.

## Implementation notes

We define $Spec$ in three consecutive steps, each with more structure than the last:

1. `Spec.to_Top`, valued in the category of topological spaces,
2. `Spec.to_SheafedSpace`, valued in the category of sheafed spaces and
3. `Spec.to_LocallyRingedSpace`, valued in the category of locally ringed spaces.

Additionally, we provide `Spec.to_PresheafedSpace` as a composition of `Spec.to_SheafedSpace` with
a forgetful functor.

## Related results

The adjunction `Γ ⊣ Spec` is constructed in `algebraic_geometry/Gamma_Spec_adjunction.lean`.

-/


noncomputable section

universe u v

namespace AlgebraicGeometry

open Opposite

open CategoryTheory

open StructureSheaf

open Spec (structureSheaf)

/-- The spectrum of a commutative ring, as a topological space.
-/
def Spec.topObj (R : CommRingₓₓ) : Top :=
  Top.of (PrimeSpectrum R)

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of topological spaces.
-/
def Spec.topMap {R S : CommRingₓₓ} (f : R ⟶ S) : Spec.topObj S ⟶ Spec.topObj R :=
  PrimeSpectrum.comap f

@[simp]
theorem Spec.Top_map_id (R : CommRingₓₓ) : Spec.topMap (𝟙 R) = 𝟙 (Spec.topObj R) :=
  PrimeSpectrum.comap_id

theorem Spec.Top_map_comp {R S T : CommRingₓₓ} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.topMap (f ≫ g) = Spec.topMap g ≫ Spec.topMap f :=
  PrimeSpectrum.comap_comp _ _

/-- The spectrum, as a contravariant functor from commutative rings to topological spaces.
-/
@[simps]
def Spec.toTop : CommRingₓₓᵒᵖ ⥤ Top where
  obj := fun R => Spec.topObj (unop R)
  map := fun R S f => Spec.topMap f.unop
  map_id' := fun R => by
    rw [unop_id, Spec.Top_map_id]
  map_comp' := fun R S T f g => by
    rw [unop_comp, Spec.Top_map_comp]

/-- The spectrum of a commutative ring, as a `SheafedSpace`.
-/
@[simps]
def Spec.sheafedSpaceObj (R : CommRingₓₓ) : SheafedSpace CommRingₓₓ where
  Carrier := Spec.topObj R
  Presheaf := (structureSheaf R).1
  IsSheaf := (structureSheaf R).2

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of sheafed spaces.
-/
@[simps]
def Spec.sheafedSpaceMap {R S : CommRingₓₓ.{u}} (f : R ⟶ S) : Spec.sheafedSpaceObj S ⟶ Spec.sheafedSpaceObj R where
  base := Spec.topMap f
  c :=
    { app := fun U => comap f (unop U) ((TopologicalSpace.Opens.map (Spec.topMap f)).obj (unop U)) fun p => id,
      naturality' := fun U V i => RingHom.ext fun s => Subtype.eq <| funext fun p => rfl }

@[simp]
theorem Spec.SheafedSpace_map_id {R : CommRingₓₓ} : Spec.sheafedSpaceMap (𝟙 R) = 𝟙 (Spec.sheafedSpaceObj R) :=
  PresheafedSpace.ext _ _ (Spec.Top_map_id R) <|
    NatTrans.ext _ _ <|
      funext fun U => by
        dsimp'
        erw [PresheafedSpace.id_c_app, comap_id]
        swap
        · rw [Spec.Top_map_id, TopologicalSpace.Opens.map_id_obj_unop]
          
        simpa [← eq_to_hom_map]

theorem Spec.SheafedSpace_map_comp {R S T : CommRingₓₓ} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.sheafedSpaceMap (f ≫ g) = Spec.sheafedSpaceMap g ≫ Spec.sheafedSpaceMap f :=
  PresheafedSpace.ext _ _ (Spec.Top_map_comp f g) <|
    NatTrans.ext _ _ <|
      funext fun U => by
        dsimp'
        rw [CategoryTheory.Functor.map_id]
        rw [category.comp_id]
        erw [comap_comp f g]
        rfl

/-- Spec, as a contravariant functor from commutative rings to sheafed spaces.
-/
@[simps]
def Spec.toSheafedSpace : CommRingₓₓᵒᵖ ⥤ SheafedSpace CommRingₓₓ where
  obj := fun R => Spec.sheafedSpaceObj (unop R)
  map := fun R S f => Spec.sheafedSpaceMap f.unop
  map_id' := fun R => by
    rw [unop_id, Spec.SheafedSpace_map_id]
  map_comp' := fun R S T f g => by
    rw [unop_comp, Spec.SheafedSpace_map_comp]

/-- Spec, as a contravariant functor from commutative rings to presheafed spaces.
-/
def Spec.toPresheafedSpace : CommRingₓₓᵒᵖ ⥤ PresheafedSpace.{u} CommRingₓₓ.{u} :=
  Spec.to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace

@[simp]
theorem Spec.to_PresheafedSpace_obj (R : CommRingₓₓᵒᵖ) :
    Spec.toPresheafedSpace.obj R = (Spec.sheafedSpaceObj (unop R)).toPresheafedSpace :=
  rfl

theorem Spec.to_PresheafedSpace_obj_op (R : CommRingₓₓ) :
    Spec.toPresheafedSpace.obj (op R) = (Spec.sheafedSpaceObj R).toPresheafedSpace :=
  rfl

@[simp]
theorem Spec.to_PresheafedSpace_map (R S : CommRingₓₓᵒᵖ) (f : R ⟶ S) :
    Spec.toPresheafedSpace.map f = Spec.sheafedSpaceMap f.unop :=
  rfl

theorem Spec.to_PresheafedSpace_map_op (R S : CommRingₓₓ) (f : R ⟶ S) :
    Spec.toPresheafedSpace.map f.op = Spec.sheafedSpaceMap f :=
  rfl

theorem Spec.basic_open_hom_ext {X : RingedSpace} {R : CommRingₓₓ} {α β : X ⟶ Spec.sheafedSpaceObj R}
    (w : α.base = β.base)
    (h :
      ∀ r : R,
        let U := PrimeSpectrum.basicOpen r
        (toOpen R U ≫ α.c.app (op U)) ≫
            X.Presheaf.map
              (eqToHom
                (by
                  rw [w])) =
          toOpen R U ≫ β.c.app (op U)) :
    α = β := by
  ext1
  · apply ((Top.Sheaf.pushforward β.base).obj X.sheaf).hom_ext _ PrimeSpectrum.is_basis_basic_opens
    intro r
    apply (structure_sheaf.to_basic_open_epi R r).1
    simpa using h r
    
  exact w

/-- The spectrum of a commutative ring, as a `LocallyRingedSpace`.
-/
@[simps]
def Spec.locallyRingedSpaceObj (R : CommRingₓₓ) : LocallyRingedSpace :=
  { Spec.sheafedSpaceObj R with
    LocalRing := fun x =>
      @RingEquiv.local_ring _
        (show LocalRing (Localization.AtPrime _) by
          infer_instance)
        _ (iso.CommRing_iso_to_ring_equiv <| stalkIso R x).symm }

@[elementwise]
theorem stalk_map_to_stalk {R S : CommRingₓₓ} (f : R ⟶ S) (p : PrimeSpectrum S) :
    toStalk R (PrimeSpectrum.comap f p) ≫ PresheafedSpace.stalkMap (Spec.sheafedSpaceMap f) p = f ≫ toStalk S p := by
  erw [← to_open_germ S ⊤ ⟨p, trivialₓ⟩, ← to_open_germ R ⊤ ⟨PrimeSpectrum.comap f p, trivialₓ⟩, category.assoc,
    PresheafedSpace.stalk_map_germ (Spec.SheafedSpace_map f) ⊤ ⟨p, trivialₓ⟩, Spec.SheafedSpace_map_c_app,
    to_open_comp_comap_assoc]
  rfl

/-- Under the isomorphisms `stalk_iso`, the map `stalk_map (Spec.SheafedSpace_map f) p` corresponds
to the induced local ring homomorphism `localization.local_ring_hom`.
-/
@[elementwise]
theorem local_ring_hom_comp_stalk_iso {R S : CommRingₓₓ} (f : R ⟶ S) (p : PrimeSpectrum S) :
    (stalkIso R (PrimeSpectrum.comap f p)).Hom ≫
        @CategoryStruct.comp _ _ (CommRingₓₓ.of (Localization.AtPrime (PrimeSpectrum.comap f p).asIdeal))
          (CommRingₓₓ.of (Localization.AtPrime p.asIdeal)) _
          (Localization.localRingHom (PrimeSpectrum.comap f p).asIdeal p.asIdeal f rfl) (stalkIso S p).inv =
      PresheafedSpace.stalkMap (Spec.sheafedSpaceMap f) p :=
  (stalkIso R (PrimeSpectrum.comap f p)).eq_inv_comp.mp <|
    (stalkIso S p).comp_inv_eq.mpr <|
      (Localization.local_ring_hom_unique _ _ _ _) fun x => by
        rw [stalk_iso_hom, stalk_iso_inv, comp_apply, comp_apply, localization_to_stalk_of, stalk_map_to_stalk_apply,
          stalk_to_fiber_ring_hom_to_stalk]

/-- The induced map of a ring homomorphism on the prime spectra, as a morphism of locally ringed spaces.
-/
@[simps]
def Spec.locallyRingedSpaceMap {R S : CommRingₓₓ} (f : R ⟶ S) :
    Spec.locallyRingedSpaceObj S ⟶ Spec.locallyRingedSpaceObj R :=
  (Subtype.mk (Spec.sheafedSpaceMap f)) fun p =>
    IsLocalRingHom.mk fun a ha => by
      -- Here, we are showing that the map on prime spectra induced by `f` is really a morphism of
      -- *locally* ringed spaces, i.e. that the induced map on the stalks is a local ring homomorphism.
      rw [← local_ring_hom_comp_stalk_iso_apply] at ha
      replace ha := (stalk_iso S p).Hom.is_unit_map ha
      rw [iso.inv_hom_id_apply] at ha
      replace ha := IsLocalRingHom.map_nonunit _ ha
      convert RingHom.is_unit_map (stalk_iso R (PrimeSpectrum.comap f p)).inv ha
      rw [iso.hom_inv_id_apply]

@[simp]
theorem Spec.LocallyRingedSpace_map_id (R : CommRingₓₓ) :
    Spec.locallyRingedSpaceMap (𝟙 R) = 𝟙 (Spec.locallyRingedSpaceObj R) :=
  Subtype.ext <| by
    rw [Spec.LocallyRingedSpace_map_coe, Spec.SheafedSpace_map_id]
    rfl

theorem Spec.LocallyRingedSpace_map_comp {R S T : CommRingₓₓ} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.locallyRingedSpaceMap (f ≫ g) = Spec.locallyRingedSpaceMap g ≫ Spec.locallyRingedSpaceMap f :=
  Subtype.ext <| by
    rw [Spec.LocallyRingedSpace_map_coe, Spec.SheafedSpace_map_comp]
    rfl

/-- Spec, as a contravariant functor from commutative rings to locally ringed spaces.
-/
@[simps]
def Spec.toLocallyRingedSpace : CommRingₓₓᵒᵖ ⥤ LocallyRingedSpace where
  obj := fun R => Spec.locallyRingedSpaceObj (unop R)
  map := fun R S f => Spec.locallyRingedSpaceMap f.unop
  map_id' := fun R => by
    rw [unop_id, Spec.LocallyRingedSpace_map_id]
  map_comp' := fun R S T f g => by
    rw [unop_comp, Spec.LocallyRingedSpace_map_comp]

section SpecΓ

open AlgebraicGeometry.LocallyRingedSpace

/-- The counit morphism `R ⟶ Γ(Spec R)` given by `algebraic_geometry.structure_sheaf.to_open`.  -/
@[simps]
def toSpecΓ (R : CommRingₓₓ) : R ⟶ Γ.obj (op (Spec.toLocallyRingedSpace.obj (op R))) :=
  StructureSheaf.toOpen R ⊤

instance is_iso_to_Spec_Γ (R : CommRingₓₓ) : IsIso (toSpecΓ R) := by
  cases R
  apply structure_sheaf.is_iso_to_global

@[reassoc]
theorem Spec_Γ_naturality {R S : CommRingₓₓ} (f : R ⟶ S) :
    f ≫ toSpecΓ S = toSpecΓ R ≫ Γ.map (Spec.toLocallyRingedSpace.map f.op).op := by
  ext
  symm
  apply Localization.local_ring_hom_to_map

/-- The counit (`Spec_Γ_identity.inv.op`) of the adjunction `Γ ⊣ Spec` is an isomorphism. -/
@[simps hom_app inv_app]
def specΓIdentity : Spec.toLocallyRingedSpace.rightOp ⋙ Γ ≅ 𝟭 _ :=
  iso.symm <| NatIso.ofComponents (fun R => asIso (toSpecΓ R) : _) fun _ _ => Spec_Γ_naturality

end SpecΓ

/-- The stalk map of `Spec M⁻¹R ⟶ Spec R` is an iso for each `p : Spec M⁻¹R`. -/
theorem Spec_map_localization_is_iso (R : CommRingₓₓ) (M : Submonoid R) (x : PrimeSpectrum (Localization M)) :
    IsIso
      (PresheafedSpace.stalkMap (Spec.toPresheafedSpace.map (CommRingₓₓ.ofHom (algebraMap R (Localization M))).op) x) :=
  by
  erw [← local_ring_hom_comp_stalk_iso]
  apply is_iso.comp_is_iso with { instances := false }
  infer_instance
  apply is_iso.comp_is_iso with { instances := false }
  -- I do not know why this is defeq to the goal, but I'm happy to accept that it is.
  exact
    show
      is_iso (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M x.as_ideal).toRingEquiv.toCommRingIso.Hom
      by
      infer_instance
  infer_instance

end AlgebraicGeometry

