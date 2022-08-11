/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.AlgebraicGeometry.Spec

/-!
# The category of schemes

A scheme is a locally ringed space such that every point is contained in some open set
where there is an isomorphism of presheaves between the restriction to that open set,
and the structure sheaf of `Spec R`, for some commutative ring `R`.

A morphism of schemes is just a morphism of the underlying locally ringed spaces.

-/


noncomputable section

open TopologicalSpace

open CategoryTheory

open Top

open Opposite

namespace AlgebraicGeometry

-- ./././Mathport/Syntax/Translate/Basic.lean:1467:11: unsupported: advanced extends in structure
/-- We define `Scheme` as a `X : LocallyRingedSpace`,
along with a proof that every point has an open neighbourhood `U`
so that that the restriction of `X` to `U` is isomorphic,
as a locally ringed space, to `Spec.to_LocallyRingedSpace.obj (op R)`
for some `R : CommRing`.
-/
structure Scheme extends
  "./././Mathport/Syntax/Translate/Basic.lean:1467:11: unsupported: advanced extends in structure" where
  local_affine :
    ∀ x : to_LocallyRingedSpace,
      ∃ (U : OpenNhds x)(R : CommRingₓₓ),
        Nonempty (to_LocallyRingedSpace.restrict U.OpenEmbedding ≅ Spec.toLocallyRingedSpace.obj (op R))

namespace Scheme

/-- Schemes are a full subcategory of locally ringed spaces.
-/
instance : Category Scheme :=
  InducedCategory.category Scheme.toLocallyRingedSpace

/-- The structure sheaf of a Scheme. -/
protected abbrev sheaf (X : Scheme) :=
  X.toSheafedSpace.Sheaf

/-- The forgetful functor from `Scheme` to `LocallyRingedSpace`. -/
@[simps]
def forgetToLocallyRingedSpace : Scheme ⥤ LocallyRingedSpace :=
  inducedFunctor _ deriving Full, Faithful

@[simp]
theorem forget_to_LocallyRingedSpace_preimage {X Y : Scheme} (f : X ⟶ Y) :
    Scheme.forgetToLocallyRingedSpace.preimage f = f :=
  rfl

/-- The forgetful functor from `Scheme` to `Top`. -/
@[simps]
def forgetToTop : Scheme ⥤ Top :=
  Scheme.forget_to_LocallyRingedSpace ⋙ LocallyRingedSpace.forget_to_Top

instance {X Y : Scheme} : HasLiftT (X ⟶ Y) (X.toSheafedSpace ⟶ Y.toSheafedSpace) :=
  @coeToLift <| @coeBaseₓ coeSubtype

theorem id_val_base (X : Scheme) : (Subtype.val (𝟙 X)).base = 𝟙 _ :=
  rfl

@[simp]
theorem id_coe_base (X : Scheme) : (↑(𝟙 X) : X.toSheafedSpace ⟶ X.toSheafedSpace).base = 𝟙 _ :=
  rfl

@[simp]
theorem id_app {X : Scheme} (U : (Opens X.Carrier)ᵒᵖ) :
    (Subtype.val (𝟙 X)).c.app U =
      X.Presheaf.map
        (eqToHom
          (by
            induction U using Opposite.rec
            cases U
            rfl)) :=
  PresheafedSpace.id_c_app X.toPresheafedSpace U

@[reassoc]
theorem comp_val {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).val = f.val ≫ g.val :=
  rfl

@[reassoc, simp]
theorem comp_coe_base {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (↑(f ≫ g) : X.toSheafedSpace ⟶ Z.toSheafedSpace).base = f.val.base ≫ g.val.base :=
  rfl

@[reassoc, elementwise]
theorem comp_val_base {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).val.base = f.val.base ≫ g.val.base :=
  rfl

@[reassoc, simp]
theorem comp_val_c_app {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (f ≫ g).val.c.app U = g.val.c.app U ≫ f.val.c.app _ :=
  rfl

theorem congr_app {X Y : Scheme} {f g : X ⟶ Y} (e : f = g) (U) :
    f.val.c.app U =
      g.val.c.app U ≫
        X.Presheaf.map
          (eqToHom
            (by
              subst e)) :=
  by
  subst e
  dsimp'
  simp

theorem app_eq {X Y : Scheme} (f : X ⟶ Y) {U V : Opens Y.Carrier} (e : U = V) :
    f.val.c.app (op U) =
      Y.Presheaf.map (eqToHom e.symm).op ≫
        f.val.c.app (op V) ≫ X.Presheaf.map (eqToHom (congr_arg (Opens.map f.val.base).obj e)).op :=
  by
  rw [← is_iso.inv_comp_eq, ← functor.map_inv, f.val.c.naturality, presheaf.pushforward_obj_map]
  congr

instance is_LocallyRingedSpace_iso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : @IsIso LocallyRingedSpace _ _ _ f :=
  forgetToLocallyRingedSpace.map_is_iso f

@[simp]
theorem inv_val_c_app {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U : Opens X.Carrier) :
    (inv f).val.c.app (op U) =
      X.Presheaf.map
          (eq_to_hom <| by
              rw [is_iso.hom_inv_id]
              ext1
              rfl :
              (Opens.map (f ≫ inv f).1.base).obj U ⟶ U).op ≫
        inv (f.val.c.app (op <| (Opens.map _).obj U)) :=
  by
  rw [is_iso.eq_comp_inv]
  erw [← Scheme.comp_val_c_app]
  rw [Scheme.congr_app (is_iso.hom_inv_id f), Scheme.id_app, ← functor.map_comp, eq_to_hom_trans, eq_to_hom_op]
  rfl

/-- The spectrum of a commutative ring, as a scheme.
-/
def specObj (R : CommRingₓₓ) : Scheme where
  local_affine := fun x => ⟨⟨⊤, trivialₓ⟩, R, ⟨(Spec.toLocallyRingedSpace.obj (op R)).restrictTopIso⟩⟩
  toLocallyRingedSpace := Spec.locallyRingedSpaceObj R

@[simp]
theorem Spec_obj_to_LocallyRingedSpace (R : CommRingₓₓ) :
    (specObj R).toLocallyRingedSpace = Spec.locallyRingedSpaceObj R :=
  rfl

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of schemes.
-/
def specMap {R S : CommRingₓₓ} (f : R ⟶ S) : specObj S ⟶ specObj R :=
  (Spec.locallyRingedSpaceMap f : Spec.locallyRingedSpaceObj S ⟶ Spec.locallyRingedSpaceObj R)

@[simp]
theorem Spec_map_id (R : CommRingₓₓ) : specMap (𝟙 R) = 𝟙 (specObj R) :=
  Spec.LocallyRingedSpace_map_id R

theorem Spec_map_comp {R S T : CommRingₓₓ} (f : R ⟶ S) (g : S ⟶ T) : specMap (f ≫ g) = specMap g ≫ specMap f :=
  Spec.LocallyRingedSpace_map_comp f g

/-- The spectrum, as a contravariant functor from commutative rings to schemes.
-/
@[simps]
def spec : CommRingₓₓᵒᵖ ⥤ Scheme where
  obj := fun R => specObj (unop R)
  map := fun R S f => specMap f.unop
  map_id' := fun R => by
    rw [unop_id, Spec_map_id]
  map_comp' := fun R S T f g => by
    rw [unop_comp, Spec_map_comp]

/-- The empty scheme, as `Spec 0`.
-/
def empty : Scheme :=
  specObj (CommRingₓₓ.of PUnit)

instance : HasEmptyc Scheme :=
  ⟨empty⟩

instance : Inhabited Scheme :=
  ⟨∅⟩

/-- The global sections, notated Gamma.
-/
def Γ : Schemeᵒᵖ ⥤ CommRingₓₓ :=
  (inducedFunctor Scheme.toLocallyRingedSpace).op ⋙ LocallyRingedSpace.Γ

theorem Γ_def : Γ = (inducedFunctor Scheme.toLocallyRingedSpace).op ⋙ LocallyRingedSpace.Γ :=
  rfl

@[simp]
theorem Γ_obj (X : Schemeᵒᵖ) : Γ.obj X = (unop X).Presheaf.obj (op ⊤) :=
  rfl

theorem Γ_obj_op (X : Scheme) : Γ.obj (op X) = X.Presheaf.obj (op ⊤) :=
  rfl

@[simp]
theorem Γ_map {X Y : Schemeᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.1.c.app (op ⊤) :=
  rfl

theorem Γ_map_op {X Y : Scheme} (f : X ⟶ Y) : Γ.map f.op = f.1.c.app (op ⊤) :=
  rfl

section BasicOpen

variable (X : Scheme) {V U : Opens X.Carrier} (f g : X.Presheaf.obj (op U))

/-- The subset of the underlying space where the given section does not vanish. -/
def basicOpen : Opens X.Carrier :=
  X.toLocallyRingedSpace.toRingedSpace.basicOpen f

@[simp]
theorem mem_basic_open (x : U) : ↑x ∈ X.basicOpen f ↔ IsUnit (X.Presheaf.germ x f) :=
  RingedSpace.mem_basic_open _ _ _

@[simp]
theorem mem_basic_open_top (f : X.Presheaf.obj (op ⊤)) (x : X.Carrier) :
    x ∈ X.basicOpen f ↔ IsUnit (X.Presheaf.germ (⟨x, trivialₓ⟩ : (⊤ : Opens _)) f) :=
  RingedSpace.mem_basic_open _ f ⟨x, trivialₓ⟩

@[simp]
theorem basic_open_res (i : op U ⟶ op V) : X.basicOpen (X.Presheaf.map i f) = V ∩ X.basicOpen f :=
  RingedSpace.basic_open_res _ i f

-- This should fire before `basic_open_res`.
@[simp]
theorem basic_open_res_eq (i : op U ⟶ op V) [IsIso i] : X.basicOpen (X.Presheaf.map i f) = X.basicOpen f :=
  RingedSpace.basic_open_res_eq _ i f

theorem basic_open_subset : X.basicOpen f ⊆ U :=
  RingedSpace.basic_open_subset _ _

theorem preimage_basic_open {X Y : Scheme} (f : X ⟶ Y) {U : Opens Y.Carrier} (r : Y.Presheaf.obj <| op U) :
    (Opens.map f.1.base).obj (Y.basicOpen r) = @Scheme.basicOpen X ((Opens.map f.1.base).obj U) (f.1.c.app _ r) :=
  LocallyRingedSpace.preimage_basic_open f r

@[simp]
theorem preimage_basic_open' {X Y : Scheme} (f : X ⟶ Y) {U : Opens Y.Carrier} (r : Y.Presheaf.obj <| op U) :
    (Opens.map (↑f : X.toSheafedSpace ⟶ Y.toSheafedSpace).base).obj (Y.basicOpen r) =
      @Scheme.basicOpen X ((Opens.map f.1.base).obj U) (f.1.c.app _ r) :=
  LocallyRingedSpace.preimage_basic_open f r

@[simp]
theorem basic_open_zero (U : Opens X.Carrier) : X.basicOpen (0 : X.Presheaf.obj <| op U) = ∅ :=
  LocallyRingedSpace.basic_open_zero _ U

@[simp]
theorem basic_open_mul : X.basicOpen (f * g) = X.basicOpen f⊓X.basicOpen g :=
  RingedSpace.basic_open_mul _ _ _

@[simp]
theorem basic_open_of_is_unit {f : X.Presheaf.obj (op U)} (hf : IsUnit f) : X.basicOpen f = U :=
  RingedSpace.basic_open_of_is_unit _ hf

end BasicOpen

end Scheme

theorem basic_open_eq_of_affine {R : CommRingₓₓ} (f : R) :
    (Scheme.spec.obj <| op R).basicOpen ((specΓIdentity.app R).inv f) = PrimeSpectrum.basicOpen f := by
  ext
  erw [Scheme.mem_basic_open_top]
  suffices IsUnit (structure_sheaf.to_stalk R x f) ↔ f ∉ PrimeSpectrum.asIdeal x by
    exact this
  erw [← is_unit_map_iff (structure_sheaf.stalk_to_fiber_ring_hom R x),
    structure_sheaf.stalk_to_fiber_ring_hom_to_stalk]
  exact
    (IsLocalization.AtPrime.is_unit_to_map_iff (Localization.AtPrime (PrimeSpectrum.asIdeal x))
      (PrimeSpectrum.asIdeal x) f :
      _)

@[simp]
theorem basic_open_eq_of_affine' {R : CommRingₓₓ} (f : (Spec.toSheafedSpace.obj (op R)).Presheaf.obj (op ⊤)) :
    (Scheme.spec.obj <| op R).basicOpen f = PrimeSpectrum.basicOpen ((specΓIdentity.app R).Hom f) := by
  convert basic_open_eq_of_affine ((Spec_Γ_identity.app R).Hom f)
  exact (iso.hom_inv_id_apply _ _).symm

end AlgebraicGeometry

