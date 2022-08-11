/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathbin.Algebra.Category.Ring.Basic
import Mathbin.Algebra.Category.Group.FilteredColimits

/-!
# The forgetful functor from (commutative) (semi-) rings preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ SemiRing`.
We show that the colimit of `F ⋙ forget₂ SemiRing Mon` (in `Mon`) carries the structure of a
semiring, thereby showing that the forgetful functor `forget₂ SemiRing Mon` preserves filtered
colimits. In particular, this implies that `forget SemiRing` preserves filtered colimits.
Similarly for `CommSemiRing`, `Ring` and `CommRing`.

-/


universe v u

noncomputable section

open Classical

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.IsFiltered renaming max → max'

-- avoid name collision with `_root_.max`.
open AddMon.FilteredColimits (colimit_zero_eq colimit_add_mk_eq)

open Mon.FilteredColimits (colimit_one_eq colimit_mul_mk_eq)

namespace SemiRing.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviations `R` and `R.mk` below, without
-- passing around `F` all the time.
parameter {J : Type v}[SmallCategory J](F : J ⥤ SemiRing.{max v u})

-- This instance is needed below in `colimit_semiring`, during the verification of the
-- semiring axioms.
instance semiringObj (j : J) : Semiringₓ (((F ⋙ forget₂ SemiRing Mon.{max v u}) ⋙ forget Mon).obj j) :=
  show Semiringₓ (F.obj j) by
    infer_instance

variable [IsFiltered J]

/-- The colimit of `F ⋙ forget₂ SemiRing Mon` in the category `Mon`.
In the following, we will show that this has the structure of a semiring.
-/
abbrev r : Mon :=
  Mon.FilteredColimits.colimit (F ⋙ forget₂ SemiRing Mon.{max v u})

instance colimitSemiring : Semiringₓ R :=
  { R.Monoid, AddCommMon.FilteredColimits.colimitAddCommMonoid (F ⋙ forget₂ SemiRing AddCommMon.{max v u}) with
    mul_zero := fun x => by
      apply Quot.induction_on x
      clear x
      intro x
      cases' x with j x
      erw [colimit_zero_eq _ j, colimit_mul_mk_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j)]
      rw [CategoryTheory.Functor.map_id, id_apply, id_apply, mul_zero x]
      rfl,
    zero_mul := fun x => by
      apply Quot.induction_on x
      clear x
      intro x
      cases' x with j x
      erw [colimit_zero_eq _ j, colimit_mul_mk_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j)]
      rw [CategoryTheory.Functor.map_id, id_apply, id_apply, zero_mul x]
      rfl,
    left_distrib := fun x y z => by
      apply Quot.induction_on₃ x y z
      clear x y z
      intro x y z
      cases' x with j₁ x
      cases' y with j₂ y
      cases' z with j₃ z
      let k := max₃ j₁ j₂ j₃
      let f := first_to_max₃ j₁ j₂ j₃
      let g := second_to_max₃ j₁ j₂ j₃
      let h := third_to_max₃ j₁ j₂ j₃
      erw [colimit_add_mk_eq _ ⟨j₂, _⟩ ⟨j₃, _⟩ k g h, colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨k, _⟩ k f (𝟙 k),
        colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨j₂, _⟩ k f g, colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨j₃, _⟩ k f h,
        colimit_add_mk_eq _ ⟨k, _⟩ ⟨k, _⟩ k (𝟙 k) (𝟙 k)]
      simp only [← CategoryTheory.Functor.map_id, ← id_apply]
      erw [left_distrib (F.map f x) (F.map g y) (F.map h z)]
      rfl,
    right_distrib := fun x y z => by
      apply Quot.induction_on₃ x y z
      clear x y z
      intro x y z
      cases' x with j₁ x
      cases' y with j₂ y
      cases' z with j₃ z
      let k := max₃ j₁ j₂ j₃
      let f := first_to_max₃ j₁ j₂ j₃
      let g := second_to_max₃ j₁ j₂ j₃
      let h := third_to_max₃ j₁ j₂ j₃
      erw [colimit_add_mk_eq _ ⟨j₁, _⟩ ⟨j₂, _⟩ k f g, colimit_mul_mk_eq _ ⟨k, _⟩ ⟨j₃, _⟩ k (𝟙 k) h,
        colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨j₃, _⟩ k f h, colimit_mul_mk_eq _ ⟨j₂, _⟩ ⟨j₃, _⟩ k g h,
        colimit_add_mk_eq _ ⟨k, _⟩ ⟨k, _⟩ k (𝟙 k) (𝟙 k)]
      simp only [← CategoryTheory.Functor.map_id, ← id_apply]
      erw [right_distrib (F.map f x) (F.map g y) (F.map h z)]
      rfl }

/-- The bundled semiring giving the filtered colimit of a diagram. -/
def colimit : SemiRing :=
  SemiRing.of R

/-- The cocone over the proposed colimit semiring. -/
def colimitCocone : cocone F where
  x := colimit
  ι :=
    { app := fun j =>
        { (Mon.FilteredColimits.colimitCocone (F ⋙ forget₂ SemiRing Mon.{max v u})).ι.app j,
          (AddCommMon.FilteredColimits.colimitCocone (F ⋙ forget₂ SemiRing AddCommMon.{max v u})).ι.app j with },
      naturality' := fun j j' f => RingHom.coe_inj ((Types.colimitCocone (F ⋙ forget SemiRing)).ι.naturality f) }

/-- The proposed colimit cocone is a colimit in `SemiRing`. -/
def colimitCoconeIsColimit : IsColimit colimit_cocone where
  desc := fun t =>
    { (Mon.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ SemiRing Mon.{max v u})).desc
        ((forget₂ SemiRing Mon.{max v u}).mapCocone t),
      (AddCommMon.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ SemiRing AddCommMon.{max v u})).desc
        ((forget₂ SemiRing AddCommMon.{max v u}).mapCocone t) with }
  fac' := fun t j =>
    RingHom.coe_inj <| (Types.colimitCoconeIsColimit (F ⋙ forget SemiRing)).fac ((forget SemiRing).mapCocone t) j
  uniq' := fun t m h =>
    RingHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget SemiRing)).uniq ((forget SemiRing).mapCocone t) m fun j =>
        funext fun x => RingHom.congr_fun (h j) x

instance forget₂MonPreservesFilteredColimits :
    PreservesFilteredColimits
      (forget₂ SemiRing
        Mon.{u}) where PreservesFilteredColimits := fun J _ _ =>
    { PreservesColimit := fun F =>
        preserves_colimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (Mon.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ SemiRing Mon.{u})) }

instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget SemiRing.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ SemiRing Mon) (forget Mon.{u})

end

end SemiRing.FilteredColimits

namespace CommSemiRing.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `R` below, without
-- passing around `F` all the time.
parameter {J : Type v}[SmallCategory J][IsFiltered J](F : J ⥤ CommSemiRing.{max v u})

/-- The colimit of `F ⋙ forget₂ CommSemiRing SemiRing` in the category `SemiRing`.
In the following, we will show that this has the structure of a _commutative_ semiring.
-/
abbrev r : SemiRing :=
  SemiRing.FilteredColimits.colimit (F ⋙ forget₂ CommSemiRing SemiRing.{max v u})

instance colimitCommSemiring : CommSemiringₓ R :=
  { R.Semiring, CommMon.FilteredColimits.colimitCommMonoid (F ⋙ forget₂ CommSemiRing CommMon.{max v u}) with }

/-- The bundled commutative semiring giving the filtered colimit of a diagram. -/
def colimit : CommSemiRing :=
  CommSemiRing.of R

/-- The cocone over the proposed colimit commutative semiring. -/
def colimitCocone : cocone F where
  x := colimit
  ι := { (SemiRing.FilteredColimits.colimitCocone (F ⋙ forget₂ CommSemiRing SemiRing.{max v u})).ι with }

/-- The proposed colimit cocone is a colimit in `CommSemiRing`. -/
def colimitCoconeIsColimit : IsColimit colimit_cocone where
  desc := fun t =>
    (SemiRing.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommSemiRing SemiRing.{max v u})).desc
      ((forget₂ CommSemiRing SemiRing).mapCocone t)
  fac' := fun t j =>
    RingHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget CommSemiRing)).fac ((forget CommSemiRing).mapCocone t) j
  uniq' := fun t m h =>
    RingHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget CommSemiRing)).uniq ((forget CommSemiRing).mapCocone t) m fun j =>
        funext fun x => RingHom.congr_fun (h j) x

instance forget₂SemiRingPreservesFilteredColimits :
    PreservesFilteredColimits
      (forget₂ CommSemiRing
        SemiRing.{u}) where PreservesFilteredColimits := fun J _ _ =>
    { PreservesColimit := fun F =>
        preserves_colimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (SemiRing.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommSemiRing SemiRing.{u})) }

instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget CommSemiRing.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ CommSemiRing SemiRing) (forget SemiRing.{u})

end

end CommSemiRing.FilteredColimits

namespace Ringₓₓ.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `R` below, without
-- passing around `F` all the time.
parameter {J : Type v}[SmallCategory J][IsFiltered J](F : J ⥤ Ringₓₓ.{max v u})

/-- The colimit of `F ⋙ forget₂ Ring SemiRing` in the category `SemiRing`.
In the following, we will show that this has the structure of a ring.
-/
abbrev r : SemiRing :=
  SemiRing.FilteredColimits.colimit (F ⋙ forget₂ Ringₓₓ SemiRing.{max v u})

instance colimitRing : Ringₓ R :=
  { R.Semiring, AddCommGroupₓₓ.FilteredColimits.colimitAddCommGroup (F ⋙ forget₂ Ringₓₓ AddCommGroupₓₓ.{max v u}) with }

/-- The bundled ring giving the filtered colimit of a diagram. -/
def colimit : Ringₓₓ :=
  Ringₓₓ.of R

/-- The cocone over the proposed colimit ring. -/
def colimitCocone : cocone F where
  x := colimit
  ι := { (SemiRing.FilteredColimits.colimitCocone (F ⋙ forget₂ Ringₓₓ SemiRing.{max v u})).ι with }

/-- The proposed colimit cocone is a colimit in `Ring`. -/
def colimitCoconeIsColimit : IsColimit colimit_cocone where
  desc := fun t =>
    (SemiRing.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ Ringₓₓ SemiRing.{max v u})).desc
      ((forget₂ Ringₓₓ SemiRing).mapCocone t)
  fac' := fun t j =>
    RingHom.coe_inj <| (Types.colimitCoconeIsColimit (F ⋙ forget Ringₓₓ)).fac ((forget Ringₓₓ).mapCocone t) j
  uniq' := fun t m h =>
    RingHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget Ringₓₓ)).uniq ((forget Ringₓₓ).mapCocone t) m fun j =>
        funext fun x => RingHom.congr_fun (h j) x

instance forget₂SemiRingPreservesFilteredColimits :
    PreservesFilteredColimits
      (forget₂ Ringₓₓ
        SemiRing.{u}) where PreservesFilteredColimits := fun J _ _ =>
    { PreservesColimit := fun F =>
        preserves_colimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (SemiRing.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ Ringₓₓ SemiRing.{u})) }

instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget Ringₓₓ.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ Ringₓₓ SemiRing) (forget SemiRing.{u})

end

end Ringₓₓ.FilteredColimits

namespace CommRingₓₓ.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `R` below, without
-- passing around `F` all the time.
parameter {J : Type v}[SmallCategory J][IsFiltered J](F : J ⥤ CommRingₓₓ.{max v u})

/-- The colimit of `F ⋙ forget₂ CommRing Ring` in the category `Ring`.
In the following, we will show that this has the structure of a _commutative_ ring.
-/
abbrev r : Ringₓₓ :=
  Ringₓₓ.FilteredColimits.colimit (F ⋙ forget₂ CommRingₓₓ Ringₓₓ.{max v u})

instance colimitCommRing : CommRingₓ R :=
  { R.Ring, CommSemiRing.FilteredColimits.colimitCommSemiring (F ⋙ forget₂ CommRingₓₓ CommSemiRing.{max v u}) with }

/-- The bundled commutative ring giving the filtered colimit of a diagram. -/
def colimit : CommRingₓₓ :=
  CommRingₓₓ.of R

/-- The cocone over the proposed colimit commutative ring. -/
def colimitCocone : cocone F where
  x := colimit
  ι := { (Ringₓₓ.FilteredColimits.colimitCocone (F ⋙ forget₂ CommRingₓₓ Ringₓₓ.{max v u})).ι with }

/-- The proposed colimit cocone is a colimit in `CommRing`. -/
def colimitCoconeIsColimit : IsColimit colimit_cocone where
  desc := fun t =>
    (Ringₓₓ.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommRingₓₓ Ringₓₓ.{max v u})).desc
      ((forget₂ CommRingₓₓ Ringₓₓ).mapCocone t)
  fac' := fun t j =>
    RingHom.coe_inj <| (Types.colimitCoconeIsColimit (F ⋙ forget CommRingₓₓ)).fac ((forget CommRingₓₓ).mapCocone t) j
  uniq' := fun t m h =>
    RingHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget CommRingₓₓ)).uniq ((forget CommRingₓₓ).mapCocone t) m fun j =>
        funext fun x => RingHom.congr_fun (h j) x

instance forget₂RingPreservesFilteredColimits :
    PreservesFilteredColimits
      (forget₂ CommRingₓₓ
        Ringₓₓ.{u}) where PreservesFilteredColimits := fun J _ _ =>
    { PreservesColimit := fun F =>
        preserves_colimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (Ringₓₓ.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommRingₓₓ Ringₓₓ.{u})) }

instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget CommRingₓₓ.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ CommRingₓₓ Ringₓₓ) (forget Ringₓₓ.{u})

end

end CommRingₓₓ.FilteredColimits

