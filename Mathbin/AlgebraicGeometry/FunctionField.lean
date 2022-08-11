/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.AlgebraicGeometry.Properties

/-!
# Function field of integral schemes

We define the function field of an irreducible scheme as the stalk of the generic point.
This is a field when the scheme is integral.

## Main definition
* `algebraic_geometry.Scheme.function_field`: The function field of an integral scheme.
* `algebraic_geometry.germ_to_function_field`: The canonical map from a component into the function
  field. This map is injective.
-/


universe u v

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits Top

namespace AlgebraicGeometry

variable (X : Scheme)

/-- The function field of an irreducible scheme is the local ring at its generic point.
Despite the name, this is a field only when the scheme is integral. -/
noncomputable abbrev Scheme.functionField [IrreducibleSpace X.Carrier] : CommRingₓₓ :=
  X.Presheaf.stalk (genericPoint X.Carrier)

/-- The restriction map from a component to the function field. -/
noncomputable abbrev Scheme.germToFunctionField [IrreducibleSpace X.Carrier] (U : Opens X.Carrier) [h : Nonempty U] :
    X.Presheaf.obj (op U) ⟶ X.functionField :=
  X.Presheaf.germ
    ⟨genericPoint X.Carrier,
      ((generic_point_spec X.Carrier).mem_open_set_iff U.Prop).mpr
        (by
          simpa using h)⟩

noncomputable instance [IrreducibleSpace X.Carrier] (U : Opens X.Carrier) [Nonempty U] :
    Algebra (X.Presheaf.obj (op U)) X.functionField :=
  (X.germToFunctionField U).toAlgebra

noncomputable instance [IsIntegral X] : Field X.functionField := by
  apply fieldOfIsUnitOrEqZero
  intro a
  obtain ⟨U, m, s, rfl⟩ := Top.Presheaf.germ_exist _ _ a
  rw [or_iff_not_imp_right, ← (X.presheaf.germ ⟨_, m⟩).map_zero]
  intro ha
  replace ha := ne_of_apply_ne _ ha
  have hs : genericPoint X.carrier ∈ RingedSpace.basic_open _ s := by
    rw [← opens.mem_coe, (generic_point_spec X.carrier).mem_open_set_iff, Set.top_eq_univ, Set.univ_inter, ←
      Set.ne_empty_iff_nonempty, Ne.def, ← opens.coe_bot, subtype.coe_injective.eq_iff, ← opens.empty_eq]
    erw [basic_open_eq_bot_iff]
    exacts[ha, (RingedSpace.basic_open _ _).Prop]
  have := (X.presheaf.germ ⟨_, hs⟩).is_unit_map (RingedSpace.is_unit_res_basic_open _ s)
  rwa [Top.Presheaf.germ_res_apply] at this

theorem germ_injective_of_is_integral [IsIntegral X] {U : Opens X.Carrier} (x : U) :
    Function.Injective (X.Presheaf.germ x) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  rw [← (X.presheaf.germ x).map_zero] at hy
  obtain ⟨W, hW, iU, iV, e⟩ := X.presheaf.germ_eq _ x.prop x.prop _ _ hy
  cases show iU = iV from Subsingleton.elimₓ _ _
  have : Nonempty W := ⟨⟨_, hW⟩⟩
  exact map_injective_of_is_integral X iU e

theorem Scheme.germ_to_function_field_injective [IsIntegral X] (U : Opens X.Carrier) [Nonempty U] :
    Function.Injective (X.germToFunctionField U) :=
  germ_injective_of_is_integral _ _

theorem generic_point_eq_of_is_open_immersion {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f]
    [hX : IrreducibleSpace X.Carrier] [IrreducibleSpace Y.Carrier] :
    f.1.base (genericPoint X.Carrier : _) = (genericPoint Y.Carrier : _) := by
  apply ((generic_point_spec _).Eq _).symm
  show T0Space Y.carrier
  · infer_instance
    
  convert
    (generic_point_spec X.carrier).Image
      (show Continuous f.1.base by
        continuity)
  symm
  rw [eq_top_iff, Set.top_eq_univ, Set.top_eq_univ]
  convert subset_closure_inter_of_is_preirreducible_of_is_open _ H.base_open.open_range _
  rw [Set.univ_inter, Set.image_univ]
  apply PreirreducibleSpace.is_preirreducible_univ with { instances := false }
  show PreirreducibleSpace Y.carrier
  · infer_instance
    
  exact ⟨_, trivialₓ, Set.mem_range_self hX.2.some⟩

noncomputable instance stalkFunctionFieldAlgebra [IrreducibleSpace X.Carrier] (x : X.Carrier) :
    Algebra (X.Presheaf.stalk x) X.functionField := by
  apply RingHom.toAlgebra
  exact X.presheaf.stalk_specializes ((generic_point_spec X.carrier).Specializes trivialₓ)

instance function_field_is_scalar_tower [IrreducibleSpace X.Carrier] (U : Opens X.Carrier) (x : U) [Nonempty U] :
    IsScalarTower (X.Presheaf.obj <| op U) (X.Presheaf.stalk x) X.functionField := by
  apply IsScalarTower.of_algebra_map_eq'
  simp_rw [RingHom.algebra_map_to_algebra]
  change _ = X.presheaf.germ x ≫ _
  rw [X.presheaf.germ_stalk_specializes]
  rfl

noncomputable instance (R : CommRingₓₓ) [IsDomain R] : Algebra R (Scheme.spec.obj <| op R).functionField :=
  RingHom.toAlgebra <| by
    change CommRingₓₓ.of R ⟶ _
    apply structure_sheaf.to_stalk

@[simp]
theorem generic_point_eq_bot_of_affine (R : CommRingₓₓ) [IsDomain R] :
    genericPoint (Scheme.spec.obj <| op R).Carrier = (⟨0, Ideal.bot_prime⟩ : PrimeSpectrum R) := by
  apply (generic_point_spec (Scheme.Spec.obj <| op R).Carrier).Eq
  simp [← is_generic_point_def, PrimeSpectrum.zero_locus_vanishing_ideal_eq_closure]

instance function_field_is_fraction_ring_of_affine (R : CommRingₓₓ.{u}) [IsDomain R] :
    IsFractionRing R (Scheme.spec.obj <| op R).functionField := by
  convert structure_sheaf.is_localization.to_stalk R _
  delta' IsFractionRing IsLocalization.AtPrime
  congr 1
  rw [generic_point_eq_bot_of_affine]
  ext
  exact mem_non_zero_divisors_iff_ne_zero

instance {X : Scheme} [IsIntegral X] {U : Opens X.Carrier} [hU : Nonempty U] :
    IsIntegral (X.restrict U.OpenEmbedding) := by
  have : Nonempty (X.restrict U.open_embedding).Carrier := hU
  exact is_integral_of_open_immersion (X.of_restrict U.open_embedding)

theorem IsAffineOpen.prime_ideal_of_generic_point {X : Scheme} [IsIntegral X] {U : Opens X.Carrier}
    (hU : IsAffineOpen U) [h : Nonempty U] :
    hU.primeIdealOf
        ⟨genericPoint X.Carrier,
          ((generic_point_spec X.Carrier).mem_open_set_iff U.Prop).mpr
            (by
              simpa using h)⟩ =
      genericPoint (Scheme.spec.obj <| op <| X.Presheaf.obj <| op U).Carrier :=
  by
  have : is_affine _ := hU
  have e : U.open_embedding.is_open_map.functor.obj ⊤ = U := by
    ext1
    exact set.image_univ.trans Subtype.range_coe
  delta' is_affine_open.prime_ideal_of
  rw [← Scheme.comp_val_base_apply]
  convert
    generic_point_eq_of_is_open_immersion
      ((X.restrict U.open_embedding).isoSpec.Hom ≫ Scheme.Spec.map (X.presheaf.map (eq_to_hom e).op).op)
  ext1
  exact (generic_point_eq_of_is_open_immersion (X.of_restrict U.open_embedding)).symm

theorem function_field_is_fraction_ring_of_is_affine_open [IsIntegral X] (U : Opens X.Carrier) (hU : IsAffineOpen U)
    [hU' : Nonempty U] : IsFractionRing (X.Presheaf.obj <| op U) X.functionField := by
  have : is_affine _ := hU
  have : Nonempty (X.restrict U.open_embedding).Carrier := hU'
  have : IsIntegral (X.restrict U.open_embedding) :=
    @is_integral_of_is_affine_is_domain _ _ _
      (by
        dsimp'
        rw [opens.open_embedding_obj_top]
        infer_instance)
  have e : U.open_embedding.is_open_map.functor.obj ⊤ = U := by
    ext1
    exact set.image_univ.trans Subtype.range_coe
  delta' IsFractionRing Scheme.function_field
  convert hU.is_localization_stalk ⟨genericPoint X.carrier, _⟩ using 1
  rw [hU.prime_ideal_of_generic_point, generic_point_eq_bot_of_affine]
  ext
  exact mem_non_zero_divisors_iff_ne_zero

instance (x : X.Carrier) : IsAffine (X.affineCover.obj x) :=
  AlgebraicGeometry.Spec_is_affine _

instance [h : IsIntegral X] (x : X.Carrier) : IsFractionRing (X.Presheaf.stalk x) X.functionField := by
  let U : opens X.carrier :=
    ⟨Set.Range (X.affine_cover.map x).1.base, PresheafedSpace.is_open_immersion.base_open.open_range⟩
  have : Nonempty U := ⟨⟨_, X.affine_cover.covers x⟩⟩
  have hU : is_affine_open U := range_is_affine_open_of_open_immersion (X.affine_cover.map x)
  exact
    @IsFractionRing.is_fraction_ring_of_is_domain_of_is_localization _ _ _ _ _ _ _ _ _ _ _
      (hU.is_localization_stalk ⟨x, X.affine_cover.covers x⟩) (function_field_is_fraction_ring_of_is_affine_open X U hU)

end AlgebraicGeometry

