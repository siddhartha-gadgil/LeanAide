/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.Algebra.Category.Ring.Constructions
import Mathbin.CategoryTheory.Isomorphism
import Mathbin.RingTheory.Localization.Away

/-!
# Properties of ring homomorphisms

We provide the basic framework for talking about properties of ring homomorphisms.
The following meta-properties of predicates on ring homomorphisms are defined

* `ring_hom.respects_iso`: `P` respects isomorphisms if `P f → P (e ≫ f)` and
  `P f → P (f ≫ e)`, where `e` is an isomorphism.
* `ring_hom.stable_under_composition`: `P` is stable under composition if `P f → P g → P (f ≫ g)`.
* `ring_hom.stable_under_base_change`: `P` is stable under base change if `P (S ⟶ Y)`
  implies `P (X ⟶ X ⊗[S] Y)`.

-/


universe u

open CategoryTheory Opposite CategoryTheory.Limits

namespace RingHom

variable (P : ∀ {R S : Type u} [CommRingₓ R] [CommRingₓ S] (f : R →+* S), Prop)

include P

section RespectsIso

/-- A property `respects_iso` if it still holds when composed with an isomorphism -/
def RespectsIso : Prop :=
  (∀ {R S T : Type u} [CommRingₓ R] [CommRingₓ S] [CommRingₓ T],
      ∀ (f : R →+* S) (e : S ≃+* T) (hf : P f), P (e.to_ring_hom.comp f)) ∧
    ∀ {R S T : Type u} [CommRingₓ R] [CommRingₓ S] [CommRingₓ T],
      ∀ (f : S →+* T) (e : R ≃+* S) (hf : P f), P (f.comp e.toRingHom)

variable {P}

theorem RespectsIso.cancel_left_is_iso (hP : RespectsIso @P) {R S T : CommRingₓₓ} (f : R ⟶ S) (g : S ⟶ T) [IsIso f] :
    P (f ≫ g) ↔ P g :=
  ⟨fun H => by
    convert hP.2 (f ≫ g) (as_iso f).symm.commRingIsoToRingEquiv H
    exact (is_iso.inv_hom_id_assoc _ _).symm, hP.2 g (asIso f).commRingIsoToRingEquiv⟩

theorem RespectsIso.cancel_right_is_iso (hP : RespectsIso @P) {R S T : CommRingₓₓ} (f : R ⟶ S) (g : S ⟶ T) [IsIso g] :
    P (f ≫ g) ↔ P f :=
  ⟨fun H => by
    convert hP.1 (f ≫ g) (as_iso g).symm.commRingIsoToRingEquiv H
    change f = f ≫ g ≫ inv g
    simp , hP.1 f (asIso g).commRingIsoToRingEquiv⟩

theorem RespectsIso.is_localization_away_iff (hP : RingHom.RespectsIso @P) {R S : Type _} (R' S' : Type _) [CommRingₓ R]
    [CommRingₓ S] [CommRingₓ R'] [CommRingₓ S'] [Algebra R R'] [Algebra S S'] (f : R →+* S) (r : R)
    [IsLocalization.Away r R'] [IsLocalization.Away (f r) S'] :
    P (Localization.awayMap f r) ↔ P (IsLocalization.Away.map R' S' f r) := by
  let e₁ : R' ≃+* Localization.Away r := (IsLocalization.algEquiv (Submonoid.powers r) _ _).toRingEquiv
  let e₂ : Localization.Away (f r) ≃+* S' := (IsLocalization.algEquiv (Submonoid.powers (f r)) _ _).toRingEquiv
  refine' (hP.cancel_left_is_iso e₁.to_CommRing_iso.hom (CommRingₓₓ.ofHom _)).symm.trans _
  refine' (hP.cancel_right_is_iso (CommRingₓₓ.ofHom _) e₂.to_CommRing_iso.hom).symm.trans _
  rw [← eq_iff_iff]
  congr 1
  dsimp' [← CommRingₓₓ.ofHom, ← CommRingₓₓ.of, ← bundled.of]
  refine' IsLocalization.ring_hom_ext (Submonoid.powers r) _
  ext1
  revert e₁ e₂
  dsimp' [← RingEquiv.toRingHom, ← IsLocalization.Away.map]
  simp only [← CategoryTheory.comp_apply, ← RingEquiv.refl_apply, ← IsLocalization.alg_equiv_apply, ←
    IsLocalization.ring_equiv_of_ring_equiv_apply, ← RingHom.coe_mk, ← RingEquiv.to_fun_eq_coe, ←
    IsLocalization.ring_equiv_of_ring_equiv_eq, ← IsLocalization.map_eq]

end RespectsIso

section StableUnderComposition

/-- A property is `stable_under_composition` if the composition of two such morphisms
still falls in the class. -/
def StableUnderComposition : Prop :=
  ∀ ⦃R S T⦄ [CommRingₓ R] [CommRingₓ S] [CommRingₓ T], ∀ (f : R →+* S) (g : S →+* T) (hf : P f) (hg : P g), P (g.comp f)

variable {P}

theorem StableUnderComposition.respects_iso (hP : RingHom.StableUnderComposition @P)
    (hP' : ∀ {R S : Type _} [CommRingₓ R] [CommRingₓ S] (e : R ≃+* S), P e.to_ring_hom) : RingHom.RespectsIso @P := by
  constructor
  · introv H
    skip
    apply hP
    exacts[H, hP' e]
    
  · introv H
    skip
    apply hP
    exacts[hP' e, H]
    

end StableUnderComposition

section StableUnderBaseChange

/-- A morphism property `P` is `stable_under_base_change` if `P(S →+* A)` implies
`P(B →+* A ⊗[S] B)`. -/
def StableUnderBaseChange : Prop :=
  ∀ ⦃R S T⦄ [CommRingₓ R] [CommRingₓ S] [CommRingₓ T],
    ∀ [Algebra R S] [Algebra R T],
      P (algebraMap R T) → P (algebra.tensor_product.include_left.to_ring_hom : S →+* TensorProduct R S T)

theorem StableUnderBaseChange.pushout_inl (hP : RingHom.StableUnderBaseChange @P) (hP' : RingHom.RespectsIso @P)
    {R S T : CommRingₓₓ} (f : R ⟶ S) (g : R ⟶ T) (H : P g) : P (pushout.inl : S ⟶ pushout f g) := by
  rw [←
    show _ = pushout.inl from
      colimit.iso_colimit_cocone_ι_inv ⟨_, CommRingₓₓ.pushoutCoconeIsColimit f g⟩ walking_span.left,
    hP'.cancel_right_is_iso]
  apply hP
  exact H

end StableUnderBaseChange

end RingHom

