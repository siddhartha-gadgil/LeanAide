/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Category.Algebra.Basic
import Mathbin.Algebra.Category.Module.Limits
import Mathbin.Algebra.Category.Ring.Limits

/-!
# The category of R-algebras has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/


open CategoryTheory

open CategoryTheory.Limits

universe v w u

-- `u` is determined by the ring, so can come last
noncomputable section

namespace AlgebraCat

variable {R : Type u} [CommRingₓ R]

variable {J : Type v} [SmallCategory J]

instance semiringObj (F : J ⥤ AlgebraCat.{max v w} R) (j) : Semiringₓ ((F ⋙ forget (AlgebraCat R)).obj j) := by
  change Semiringₓ (F.obj j)
  infer_instance

instance algebraObj (F : J ⥤ AlgebraCat.{max v w} R) (j) : Algebra R ((F ⋙ forget (AlgebraCat R)).obj j) := by
  change Algebra R (F.obj j)
  infer_instance

/-- The flat sections of a functor into `Algebra R` form a submodule of all sections.
-/
def sectionsSubalgebra (F : J ⥤ AlgebraCat.{max v w} R) : Subalgebra R (∀ j, F.obj j) :=
  { SemiRing.sectionsSubsemiring (F ⋙ forget₂ (AlgebraCat R) Ringₓₓ.{max v w} ⋙ forget₂ Ringₓₓ SemiRing.{max v w}) with
    algebra_map_mem' := fun r j j' f => (F.map f).commutes r }

instance limitSemiring (F : J ⥤ AlgebraCat.{max v w} R) :
    Ringₓ (Types.limitCone (F ⋙ forget (AlgebraCat.{max v w} R))).x := by
  change Ringₓ (sections_subalgebra F)
  infer_instance

instance limitAlgebra (F : J ⥤ AlgebraCat.{max v w} R) :
    Algebra R (Types.limitCone (F ⋙ forget (AlgebraCat.{max v w} R))).x := by
  have : Algebra R (types.limit_cone (F ⋙ forget (AlgebraCat.{max v w} R))).x = Algebra R (sections_subalgebra F) := by
    rfl
  rw [this]
  infer_instance

/-- `limit.π (F ⋙ forget (Algebra R)) j` as a `alg_hom`. -/
def limitπAlgHom (F : J ⥤ AlgebraCat.{max v w} R) (j) :
    (Types.limitCone (F ⋙ forget (AlgebraCat R))).x →ₐ[R] (F ⋙ forget (AlgebraCat.{max v w} R)).obj j :=
  { SemiRing.limitπRingHom (F ⋙ forget₂ (AlgebraCat R) Ringₓₓ.{max v w} ⋙ forget₂ Ringₓₓ SemiRing.{max v w}) j with
    commutes' := fun r => rfl }

namespace HasLimits

/-- Construction of a limit cone in `Algebra R`.
(Internal use only; use the limits API.)
-/
-- The next two definitions are used in the construction of `has_limits (Algebra R)`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.
def limitCone (F : J ⥤ AlgebraCat.{max v w} R) : Cone F where
  x := AlgebraCat.of R (Types.limitCone (F ⋙ forget _)).x
  π :=
    { app := limitπAlgHom F,
      naturality' := fun j j' f => AlgHom.coe_fn_injective ((Types.limitCone (F ⋙ forget _)).π.naturality f) }

/-- Witness that the limit cone in `Algebra R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limitConeIsLimit (F : J ⥤ AlgebraCat.{max v w} R) : IsLimit (limitCone F) := by
  refine' is_limit.of_faithful (forget (AlgebraCat R)) (types.limit_cone_is_limit _) (fun s => { .. }) fun s => rfl
  · simp only [← forget_map_eq_coe, ← AlgHom.map_one, ← functor.map_cone_π_app]
    rfl
    
  · intro x y
    simp only [← forget_map_eq_coe, ← AlgHom.map_mul, ← functor.map_cone_π_app]
    rfl
    
  · simp only [← forget_map_eq_coe, ← AlgHom.map_zero, ← functor.map_cone_π_app]
    rfl
    
  · intro x y
    simp only [← forget_map_eq_coe, ← AlgHom.map_add, ← functor.map_cone_π_app]
    rfl
    
  · intro r
    ext j
    exact (s.π.app j).commutes r
    

end HasLimits

open HasLimits

-- ./././Mathport/Syntax/Translate/Basic.lean:1389:38: unsupported irreducible non-definition
/-- The category of R-algebras has all limits. -/
irreducible_def has_limits_of_size : HasLimitsOfSize.{v, v} (AlgebraCat.{max v w} R) :=
  { HasLimitsOfShape := fun J 𝒥 =>
      { HasLimit := fun F => has_limit.mk { Cone := limit_cone F, IsLimit := limit_cone_is_limit F } } }

instance has_limits : HasLimits (AlgebraCat.{w} R) :=
  AlgebraCat.has_limits_of_size.{w, w, u}

/-- The forgetful functor from R-algebras to rings preserves all limits.
-/
instance forget₂RingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget₂ (AlgebraCat R)
        Ringₓₓ.{max v
            w}) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (by
            apply Ringₓₓ.limitConeIsLimit (F ⋙ forget₂ (AlgebraCat R) Ringₓₓ.{max v w})) }

instance forget₂RingPreservesLimits : PreservesLimits (forget₂ (AlgebraCat R) Ringₓₓ.{w}) :=
  AlgebraCat.forget₂RingPreservesLimitsOfSize.{w, w}

/-- The forgetful functor from R-algebras to R-modules preserves all limits.
-/
instance forget₂ModulePreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget₂ (AlgebraCat R)
        (ModuleCat.{max v w}
          R)) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (by
            apply ModuleCat.HasLimits.limitConeIsLimit (F ⋙ forget₂ (AlgebraCat R) (ModuleCat.{max v w} R))) }

instance forget₂ModulePreservesLimits : PreservesLimits (forget₂ (AlgebraCat R) (ModuleCat.{w} R)) :=
  AlgebraCat.forget₂ModulePreservesLimitsOfSize.{w, w}

/-- The forgetful functor from R-algebras to types preserves all limits.
-/
instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget
        (AlgebraCat.{max v w}
          R)) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F) (types.limit_cone_is_limit (F ⋙ forget _)) }

instance forgetPreservesLimits : PreservesLimits (forget (AlgebraCat.{w} R)) :=
  AlgebraCat.forgetPreservesLimitsOfSize.{w, w}

end AlgebraCat

