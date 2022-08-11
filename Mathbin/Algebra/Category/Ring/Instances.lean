/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.Algebra.Category.Ring.Basic
import Mathbin.RingTheory.Localization.Away

/-!
# Ring-theoretic results in terms of categorical languages
-/


open CategoryTheory

instance localization_unit_is_iso (R : CommRingₓₓ) :
    IsIso (CommRingₓₓ.ofHom <| algebraMap R (Localization.Away (1 : R))) :=
  IsIso.of_iso (IsLocalization.atOne R (Localization.Away (1 : R))).toRingEquiv.toCommRingIso

instance localization_unit_is_iso' (R : CommRingₓₓ) :
    @IsIso CommRingₓₓ _ R _ (CommRingₓₓ.ofHom <| algebraMap R (Localization.Away (1 : R))) := by
  cases R
  exact localization_unit_is_iso _

