/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Punit
import Mathbin.CategoryTheory.Limits.HasLimits

/-!
# `discrete punit` has limits and colimits

Mostly for the sake of constructing trivial examples, we show all (co)cones into `discrete punit`
are (co)limit (co)cones. We also show that such (co)cones exist, and that `discrete punit` has all
(co)limits.
-/


universe v

open CategoryTheory

namespace CategoryTheory.Limits

variable {J : Type v} [SmallCategory J] {F : J ⥤ Discrete PUnit}

/-- A trivial cone for a functor into `punit`. `punit_cone_is_limit` shows it is a limit. -/
def punitCone : Cone F :=
  ⟨⟨⟨⟩⟩, (Functor.punitExt _ _).Hom⟩

/-- A trivial cocone for a functor into `punit`. `punit_cocone_is_limit` shows it is a colimit. -/
def punitCocone : Cocone F :=
  ⟨⟨⟨⟩⟩, (Functor.punitExt _ _).Hom⟩

/-- Any cone over a functor into `punit` is a limit cone.
-/
def punitConeIsLimit {c : Cone F} : IsLimit c := by
  tidy

/-- Any cocone over a functor into `punit` is a colimit cocone.
-/
def punitCoconeIsColimit {c : Cocone F} : IsColimit c := by
  tidy

instance : HasLimits (Discrete PUnit) := by
  tidy

instance : HasColimits (Discrete PUnit) := by
  tidy

end CategoryTheory.Limits

