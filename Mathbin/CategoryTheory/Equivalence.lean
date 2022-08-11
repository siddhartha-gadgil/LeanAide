/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import Mathbin.CategoryTheory.Functor.FullyFaithful
import Mathbin.CategoryTheory.FullSubcategory
import Mathbin.CategoryTheory.Whiskering
import Mathbin.CategoryTheory.EssentialImage
import Mathbin.Tactic.Slice

/-!
# Equivalence of categories

An equivalence of categories `C` and `D` is a pair of functors `F : C ⥤ D` and `G : D ⥤ C` such
that `η : 𝟭 C ≅ F ⋙ G` and `ε : G ⋙ F ≅ 𝟭 D`. In many situations, equivalences are a better
notion of "sameness" of categories than the stricter isomorphims of categories.

Recall that one way to express that two functors `F : C ⥤ D` and `G : D ⥤ C` are adjoint is using
two natural transformations `η : 𝟭 C ⟶ F ⋙ G` and `ε : G ⋙ F ⟶ 𝟭 D`, called the unit and the
counit, such that the compositions `F ⟶ FGF ⟶ F` and `G ⟶ GFG ⟶ G` are the identity. Unfortunately,
it is not the case that the natural isomorphisms `η` and `ε` in the definition of an equivalence
automatically give an adjunction. However, it is true that
* if one of the two compositions is the identity, then so is the other, and
* given an equivalence of categories, it is always possible to refine `η` in such a way that the
  identities are satisfied.

For this reason, in mathlib we define an equivalence to be a "half-adjoint equivalence", which is
a tuple `(F, G, η, ε)` as in the first paragraph such that the composite `F ⟶ FGF ⟶ F` is the
identity. By the remark above, this already implies that the tuple is an "adjoint equivalence",
i.e., that the composite `G ⟶ GFG ⟶ G` is also the identity.

We also define essentially surjective functors and show that a functor is an equivalence if and only
if it is full, faithful and essentially surjective.

## Main definitions

* `equivalence`: bundled (half-)adjoint equivalences of categories
* `is_equivalence`: type class on a functor `F` containing the data of the inverse `G` as well as
  the natural isomorphisms `η` and `ε`.
* `ess_surj`: type class on a functor `F` containing the data of the preimages and the isomorphisms
  `F.obj (preimage d) ≅ d`.

## Main results

* `equivalence.mk`: upgrade an equivalence to a (half-)adjoint equivalence
* `is_equivalence.equiv_of_iso`: when `F` and `G` are isomorphic functors, `F` is an equivalence
iff `G` is.
* `equivalence.of_fully_faithfully_ess_surj`: a fully faithful essentially surjective functor is an
  equivalence.

## Notations

We write `C ≌ D` (`\backcong`, not to be confused with `≅`/`\cong`) for a bundled equivalence.

-/


namespace CategoryTheory

open CategoryTheory.Functor NatIso Category

-- declare the `v`'s first; see `category_theory.category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

/-- We define an equivalence as a (half)-adjoint equivalence, a pair of functors with
  a unit and counit which are natural isomorphisms and the triangle law `Fη ≫ εF = 1`, or in other
  words the composite `F ⟶ FGF ⟶ F` is the identity.

  In `unit_inverse_comp`, we show that this is actually an adjoint equivalence, i.e., that the
  composite `G ⟶ GFG ⟶ G` is also the identity.

  The triangle equation is written as a family of equalities between morphisms, it is more
  complicated if we write it as an equality of natural transformations, because then we would have
  to insert natural transformations like `F ⟶ F1`.

See <https://stacks.math.columbia.edu/tag/001J>
-/
structure Equivalence (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] where mk' ::
  Functor : C ⥤ D
  inverse : D ⥤ C
  unitIso : 𝟭 C ≅ Functor ⋙ inverse
  counitIso : inverse ⋙ Functor ≅ 𝟭 D
  functor_unit_iso_comp' :
    ∀ X : C,
      Functor.map ((unit_iso.Hom : 𝟭 C ⟶ Functor ⋙ inverse).app X) ≫ counit_iso.Hom.app (Functor.obj X) =
        𝟙 (Functor.obj X) := by
    run_tac
      obviously

restate_axiom equivalence.functor_unit_iso_comp'

-- mathport name: «expr ≌ »
infixr:10 " ≌ " => Equivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Equivalenceₓ

/-- The unit of an equivalence of categories. -/
abbrev unit (e : C ≌ D) : 𝟭 C ⟶ e.Functor ⋙ e.inverse :=
  e.unitIso.Hom

/-- The counit of an equivalence of categories. -/
abbrev counit (e : C ≌ D) : e.inverse ⋙ e.Functor ⟶ 𝟭 D :=
  e.counitIso.Hom

/-- The inverse of the unit of an equivalence of categories. -/
abbrev unitInv (e : C ≌ D) : e.Functor ⋙ e.inverse ⟶ 𝟭 C :=
  e.unitIso.inv

/-- The inverse of the counit of an equivalence of categories. -/
abbrev counitInv (e : C ≌ D) : 𝟭 D ⟶ e.inverse ⋙ e.Functor :=
  e.counitIso.inv

/- While these abbreviations are convenient, they also cause some trouble,
preventing structure projections from unfolding. -/
@[simp]
theorem equivalence_mk'_unit (functor inverse unit_iso counit_iso f) :
    (⟨Functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).Unit = unit_iso.Hom :=
  rfl

@[simp]
theorem equivalence_mk'_counit (functor inverse unit_iso counit_iso f) :
    (⟨Functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).counit = counit_iso.Hom :=
  rfl

@[simp]
theorem equivalence_mk'_unit_inv (functor inverse unit_iso counit_iso f) :
    (⟨Functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).unitInv = unit_iso.inv :=
  rfl

@[simp]
theorem equivalence_mk'_counit_inv (functor inverse unit_iso counit_iso f) :
    (⟨Functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).counitInv = counit_iso.inv :=
  rfl

@[simp]
theorem functor_unit_comp (e : C ≌ D) (X : C) :
    e.Functor.map (e.Unit.app X) ≫ e.counit.app (e.Functor.obj X) = 𝟙 (e.Functor.obj X) :=
  e.functor_unit_iso_comp X

@[simp]
theorem counit_inv_functor_comp (e : C ≌ D) (X : C) :
    e.counitInv.app (e.Functor.obj X) ≫ e.Functor.map (e.unitInv.app X) = 𝟙 (e.Functor.obj X) := by
  erw [iso.inv_eq_inv (e.functor.map_iso (e.unit_iso.app X) ≪≫ e.counit_iso.app (e.functor.obj X)) (iso.refl _)]
  exact e.functor_unit_comp X

theorem counit_inv_app_functor (e : C ≌ D) (X : C) : e.counitInv.app (e.Functor.obj X) = e.Functor.map (e.Unit.app X) :=
  by
  symm
  erw [← iso.comp_hom_eq_id (e.counit_iso.app _), functor_unit_comp]
  rfl

theorem counit_app_functor (e : C ≌ D) (X : C) : e.counit.app (e.Functor.obj X) = e.Functor.map (e.unitInv.app X) := by
  erw [← iso.hom_comp_eq_id (e.functor.map_iso (e.unit_iso.app X)), functor_unit_comp]
  rfl

/-- The other triangle equality. The proof follows the following proof in Globular:
  http://globular.science/1905.001 -/
@[simp]
theorem unit_inverse_comp (e : C ≌ D) (Y : D) :
    e.Unit.app (e.inverse.obj Y) ≫ e.inverse.map (e.counit.app Y) = 𝟙 (e.inverse.obj Y) := by
  rw [← id_comp (e.inverse.map _), ← map_id e.inverse, ← counit_inv_functor_comp, map_comp, ←
    iso.hom_inv_id_assoc (e.unit_iso.app _) (e.inverse.map (e.functor.map _)), app_hom, app_inv]
  slice_lhs 2 3 => erw [e.unit.naturality]
  slice_lhs 1 2 => erw [e.unit.naturality]
  slice_lhs 4 4 => rw [← iso.hom_inv_id_assoc (e.inverse.map_iso (e.counit_iso.app _)) (e.unit_inv.app _)]
  slice_lhs 3 4 => erw [← map_comp e.inverse, e.counit.naturality]erw [(e.counit_iso.app _).hom_inv_id, map_id]
  erw [id_comp]
  slice_lhs 2 3 => erw [← map_comp e.inverse, e.counit_iso.inv.naturality, map_comp]
  slice_lhs 3 4 => erw [e.unit_inv.naturality]
  slice_lhs 4 5 => erw [← map_comp (e.functor ⋙ e.inverse), (e.unit_iso.app _).hom_inv_id, map_id]
  erw [id_comp]
  slice_lhs 3 4 => erw [← e.unit_inv.naturality]
  slice_lhs 2 3 => erw [← map_comp e.inverse, ← e.counit_iso.inv.naturality, (e.counit_iso.app _).hom_inv_id, map_id]
  erw [id_comp, (e.unit_iso.app _).hom_inv_id]
  rfl

@[simp]
theorem inverse_counit_inv_comp (e : C ≌ D) (Y : D) :
    e.inverse.map (e.counitInv.app Y) ≫ e.unitInv.app (e.inverse.obj Y) = 𝟙 (e.inverse.obj Y) := by
  erw [iso.inv_eq_inv (e.unit_iso.app (e.inverse.obj Y) ≪≫ e.inverse.map_iso (e.counit_iso.app Y)) (iso.refl _)]
  exact e.unit_inverse_comp Y

theorem unit_app_inverse (e : C ≌ D) (Y : D) : e.Unit.app (e.inverse.obj Y) = e.inverse.map (e.counitInv.app Y) := by
  erw [← iso.comp_hom_eq_id (e.inverse.map_iso (e.counit_iso.app Y)), unit_inverse_comp]
  rfl

theorem unit_inv_app_inverse (e : C ≌ D) (Y : D) : e.unitInv.app (e.inverse.obj Y) = e.inverse.map (e.counit.app Y) :=
  by
  symm
  erw [← iso.hom_comp_eq_id (e.unit_iso.app _), unit_inverse_comp]
  rfl

@[simp]
theorem fun_inv_map (e : C ≌ D) (X Y : D) (f : X ⟶ Y) :
    e.Functor.map (e.inverse.map f) = e.counit.app X ≫ f ≫ e.counitInv.app Y :=
  (NatIso.naturality_2 e.counitIso f).symm

@[simp]
theorem inv_fun_map (e : C ≌ D) (X Y : C) (f : X ⟶ Y) :
    e.inverse.map (e.Functor.map f) = e.unitInv.app X ≫ f ≫ e.Unit.app Y :=
  (NatIso.naturality_1 e.unitIso f).symm

section

-- In this section we convert an arbitrary equivalence to a half-adjoint equivalence.
variable {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D)

/-- If `η : 𝟭 C ≅ F ⋙ G` is part of a (not necessarily half-adjoint) equivalence, we can upgrade it
to a refined natural isomorphism `adjointify_η η : 𝟭 C ≅ F ⋙ G` which exhibits the properties
required for a half-adjoint equivalence. See `equivalence.mk`. -/
def adjointifyη : 𝟭 C ≅ F ⋙ G :=
  calc
    𝟭 C ≅ F ⋙ G := η
    _ ≅ F ⋙ 𝟭 D ⋙ G := isoWhiskerLeft F (leftUnitor G).symm
    _ ≅ F ⋙ (G ⋙ F) ⋙ G := isoWhiskerLeft F (isoWhiskerRight ε.symm G)
    _ ≅ F ⋙ G ⋙ F ⋙ G := isoWhiskerLeft F (associator G F G)
    _ ≅ (F ⋙ G) ⋙ F ⋙ G := (associator F G (F ⋙ G)).symm
    _ ≅ 𝟭 C ⋙ F ⋙ G := isoWhiskerRight η.symm (F ⋙ G)
    _ ≅ F ⋙ G := leftUnitor (F ⋙ G)
    

theorem adjointify_η_ε (X : C) : F.map ((adjointifyη η ε).Hom.app X) ≫ ε.Hom.app (F.obj X) = 𝟙 (F.obj X) := by
  dsimp' [← adjointify_η]
  simp
  have := ε.hom.naturality (F.map (η.inv.app X))
  dsimp'  at this
  rw [this]
  clear this
  rw [← assoc _ _ (F.map _)]
  have := ε.hom.naturality (ε.inv.app <| F.obj X)
  dsimp'  at this
  rw [this]
  clear this
  have := (ε.app <| F.obj X).hom_inv_id
  dsimp'  at this
  rw [this]
  clear this
  rw [id_comp]
  have := (F.map_iso <| η.app X).hom_inv_id
  dsimp'  at this
  rw [this]

end

/-- Every equivalence of categories consisting of functors `F` and `G` such that `F ⋙ G` and
    `G ⋙ F` are naturally isomorphic to identity functors can be transformed into a half-adjoint
    equivalence without changing `F` or `G`. -/
protected def mk (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) : C ≌ D :=
  ⟨F, G, adjointifyη η ε, ε, adjointify_η_ε η ε⟩

/-- Equivalence of categories is reflexive. -/
@[refl, simps]
def refl : C ≌ C :=
  ⟨𝟭 C, 𝟭 C, Iso.refl _, Iso.refl _, fun X => Category.id_comp _⟩

instance : Inhabited (C ≌ C) :=
  ⟨refl⟩

/-- Equivalence of categories is symmetric. -/
@[symm, simps]
def symm (e : C ≌ D) : D ≌ C :=
  ⟨e.inverse, e.Functor, e.counitIso.symm, e.unitIso.symm, e.inverse_counit_inv_comp⟩

variable {E : Type u₃} [Category.{v₃} E]

/-- Equivalence of categories is transitive. -/
@[trans, simps]
def trans (e : C ≌ D) (f : D ≌ E) : C ≌ E where
  Functor := e.Functor ⋙ f.Functor
  inverse := f.inverse ⋙ e.inverse
  unitIso := by
    refine' iso.trans e.unit_iso _
    exact iso_whisker_left e.functor (iso_whisker_right f.unit_iso e.inverse)
  counitIso := by
    refine' iso.trans _ f.counit_iso
    exact iso_whisker_left f.inverse (iso_whisker_right e.counit_iso f.functor)
  -- We wouldn't have needed to give this proof if we'd used `equivalence.mk`,
  -- but we choose to avoid using that here, for the sake of good structure projection `simp`
  -- lemmas.
  functor_unit_iso_comp' := fun X => by
    dsimp'
    rw [← f.functor.map_comp_assoc, e.functor.map_comp, ← counit_inv_app_functor, fun_inv_map, iso.inv_hom_id_app_assoc,
      assoc, iso.inv_hom_id_app, counit_app_functor, ← functor.map_comp]
    erw [comp_id, iso.hom_inv_id_app, Functor.map_id]

/-- Composing a functor with both functors of an equivalence yields a naturally isomorphic
functor. -/
def funInvIdAssoc (e : C ≌ D) (F : C ⥤ E) : e.Functor ⋙ e.inverse ⋙ F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.unitIso.symm F ≪≫ F.leftUnitor

@[simp]
theorem fun_inv_id_assoc_hom_app (e : C ≌ D) (F : C ⥤ E) (X : C) :
    (funInvIdAssoc e F).Hom.app X = F.map (e.unitInv.app X) := by
  dsimp' [← fun_inv_id_assoc]
  tidy

@[simp]
theorem fun_inv_id_assoc_inv_app (e : C ≌ D) (F : C ⥤ E) (X : C) :
    (funInvIdAssoc e F).inv.app X = F.map (e.Unit.app X) := by
  dsimp' [← fun_inv_id_assoc]
  tidy

/-- Composing a functor with both functors of an equivalence yields a naturally isomorphic
functor. -/
def invFunIdAssoc (e : C ≌ D) (F : D ⥤ E) : e.inverse ⋙ e.Functor ⋙ F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.counitIso F ≪≫ F.leftUnitor

@[simp]
theorem inv_fun_id_assoc_hom_app (e : C ≌ D) (F : D ⥤ E) (X : D) :
    (invFunIdAssoc e F).Hom.app X = F.map (e.counit.app X) := by
  dsimp' [← inv_fun_id_assoc]
  tidy

@[simp]
theorem inv_fun_id_assoc_inv_app (e : C ≌ D) (F : D ⥤ E) (X : D) :
    (invFunIdAssoc e F).inv.app X = F.map (e.counitInv.app X) := by
  dsimp' [← inv_fun_id_assoc]
  tidy

/-- If `C` is equivalent to `D`, then `C ⥤ E` is equivalent to `D ⥤ E`. -/
@[simps Functor inverse unitIso counitIso]
def congrLeft (e : C ≌ D) : C ⥤ E ≌ D ⥤ E :=
  Equivalence.mk ((whiskeringLeft _ _ _).obj e.inverse) ((whiskeringLeft _ _ _).obj e.Functor)
    (NatIso.ofComponents (fun F => (e.funInvIdAssoc F).symm)
      (by
        tidy))
    (NatIso.ofComponents (fun F => e.invFunIdAssoc F)
      (by
        tidy))

/-- If `C` is equivalent to `D`, then `E ⥤ C` is equivalent to `E ⥤ D`. -/
@[simps Functor inverse unitIso counitIso]
def congrRight (e : C ≌ D) : E ⥤ C ≌ E ⥤ D :=
  Equivalence.mk ((whiskeringRight _ _ _).obj e.Functor) ((whiskeringRight _ _ _).obj e.inverse)
    (NatIso.ofComponents (fun F => F.rightUnitor.symm ≪≫ isoWhiskerLeft F e.unitIso ≪≫ Functor.associator _ _ _)
      (by
        tidy))
    (NatIso.ofComponents (fun F => Functor.associator _ _ _ ≪≫ isoWhiskerLeft F e.counitIso ≪≫ F.rightUnitor)
      (by
        tidy))

section CancellationLemmas

variable (e : C ≌ D)

/- We need special forms of `cancel_nat_iso_hom_right(_assoc)` and
`cancel_nat_iso_inv_right(_assoc)` for units and counits, because neither `simp` or `rw` will apply
those lemmas in this setting without providing `e.unit_iso` (or similar) as an explicit argument.
We also provide the lemmas for length four compositions, since they're occasionally useful.
(e.g. in proving that equivalences take monos to monos) -/
@[simp]
theorem cancel_unit_right {X Y : C} (f f' : X ⟶ Y) : f ≫ e.Unit.app Y = f' ≫ e.Unit.app Y ↔ f = f' := by
  simp only [← cancel_mono]

@[simp]
theorem cancel_unit_inv_right {X Y : C} (f f' : X ⟶ e.inverse.obj (e.Functor.obj Y)) :
    f ≫ e.unitInv.app Y = f' ≫ e.unitInv.app Y ↔ f = f' := by
  simp only [← cancel_mono]

@[simp]
theorem cancel_counit_right {X Y : D} (f f' : X ⟶ e.Functor.obj (e.inverse.obj Y)) :
    f ≫ e.counit.app Y = f' ≫ e.counit.app Y ↔ f = f' := by
  simp only [← cancel_mono]

@[simp]
theorem cancel_counit_inv_right {X Y : D} (f f' : X ⟶ Y) : f ≫ e.counitInv.app Y = f' ≫ e.counitInv.app Y ↔ f = f' := by
  simp only [← cancel_mono]

@[simp]
theorem cancel_unit_right_assoc {W X X' Y : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y) :
    f ≫ g ≫ e.Unit.app Y = f' ≫ g' ≫ e.Unit.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [category.assoc, ← cancel_mono]

@[simp]
theorem cancel_counit_inv_right_assoc {W X X' Y : D} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y) :
    f ≫ g ≫ e.counitInv.app Y = f' ≫ g' ≫ e.counitInv.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [category.assoc, ← cancel_mono]

@[simp]
theorem cancel_unit_right_assoc' {W X X' Y Y' Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (f' : W ⟶ X') (g' : X' ⟶ Y')
    (h' : Y' ⟶ Z) : f ≫ g ≫ h ≫ e.Unit.app Z = f' ≫ g' ≫ h' ≫ e.Unit.app Z ↔ f ≫ g ≫ h = f' ≫ g' ≫ h' := by
  simp only [category.assoc, ← cancel_mono]

@[simp]
theorem cancel_counit_inv_right_assoc' {W X X' Y Y' Z : D} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (f' : W ⟶ X')
    (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
    f ≫ g ≫ h ≫ e.counitInv.app Z = f' ≫ g' ≫ h' ≫ e.counitInv.app Z ↔ f ≫ g ≫ h = f' ≫ g' ≫ h' := by
  simp only [category.assoc, ← cancel_mono]

end CancellationLemmas

section

/-- Natural number powers of an auto-equivalence.  Use `(^)` instead. -/
-- There's of course a monoid structure on `C ≌ C`,
-- but let's not encourage using it.
-- The power structure is nevertheless useful.
def powNatₓ (e : C ≌ C) : ℕ → (C ≌ C)
  | 0 => Equivalence.refl
  | 1 => e
  | n + 2 => e.trans (pow_nat (n + 1))

/-- Powers of an auto-equivalence.  Use `(^)` instead. -/
def powₓ (e : C ≌ C) : ℤ → (C ≌ C)
  | Int.ofNat n => e.powNat n
  | Int.negSucc n => e.symm.powNat (n + 1)

instance : Pow (C ≌ C) ℤ :=
  ⟨powₓ⟩

@[simp]
theorem pow_zero (e : C ≌ C) : e ^ (0 : ℤ) = equivalence.refl :=
  rfl

@[simp]
theorem pow_one (e : C ≌ C) : e ^ (1 : ℤ) = e :=
  rfl

@[simp]
theorem pow_neg_one (e : C ≌ C) : e ^ (-1 : ℤ) = e.symm :=
  rfl

-- TODO as necessary, add the natural isomorphisms `(e^a).trans e^b ≅ e^(a+b)`.
-- At this point, we haven't even defined the category of equivalences.
end

end Equivalenceₓ

/-- A functor that is part of a (half) adjoint equivalence -/
class IsEquivalence (F : C ⥤ D) where mk' ::
  inverse : D ⥤ C
  unitIso : 𝟭 C ≅ F ⋙ inverse
  counitIso : inverse ⋙ F ≅ 𝟭 D
  functor_unit_iso_comp' :
    ∀ X : C, F.map ((unit_iso.Hom : 𝟭 C ⟶ F ⋙ inverse).app X) ≫ counit_iso.Hom.app (F.obj X) = 𝟙 (F.obj X) := by
    run_tac
      obviously

restate_axiom is_equivalence.functor_unit_iso_comp'

attribute [simp, reassoc] is_equivalence.functor_unit_iso_comp

namespace IsEquivalence

instance ofEquivalence (F : C ≌ D) : IsEquivalence F.Functor :=
  { F with }

instance ofEquivalenceInverse (F : C ≌ D) : IsEquivalence F.inverse :=
  IsEquivalence.ofEquivalence F.symm

open Equivalenceₓ

/-- To see that a functor is an equivalence, it suffices to provide an inverse functor `G` such that
    `F ⋙ G` and `G ⋙ F` are naturally isomorphic to identity functors. -/
protected def mk {F : C ⥤ D} (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) : IsEquivalence F :=
  ⟨G, adjointifyη η ε, ε, adjointify_η_ε η ε⟩

end IsEquivalence

namespace Functor

/-- Interpret a functor that is an equivalence as an equivalence. -/
def asEquivalence (F : C ⥤ D) [IsEquivalence F] : C ≌ D :=
  ⟨F, IsEquivalence.inverse F, IsEquivalence.unitIso, IsEquivalence.counitIso, IsEquivalence.functor_unit_iso_comp⟩

instance isEquivalenceRefl : IsEquivalence (𝟭 C) :=
  IsEquivalence.ofEquivalence Equivalence.refl

/-- The inverse functor of a functor that is an equivalence. -/
def inv (F : C ⥤ D) [IsEquivalence F] : D ⥤ C :=
  IsEquivalence.inverse F

instance isEquivalenceInv (F : C ⥤ D) [IsEquivalence F] : IsEquivalence F.inv :=
  IsEquivalence.ofEquivalence F.asEquivalence.symm

@[simp]
theorem as_equivalence_functor (F : C ⥤ D) [IsEquivalence F] : F.asEquivalence.Functor = F :=
  rfl

@[simp]
theorem as_equivalence_inverse (F : C ⥤ D) [IsEquivalence F] : F.asEquivalence.inverse = inv F :=
  rfl

@[simp]
theorem as_equivalence_unit {F : C ⥤ D} [h : IsEquivalence F] :
    F.asEquivalence.unitIso = @IsEquivalence.unitIso _ _ h :=
  rfl

@[simp]
theorem as_equivalence_counit {F : C ⥤ D} [IsEquivalence F] : F.asEquivalence.counitIso = is_equivalence.counit_iso :=
  rfl

@[simp]
theorem inv_inv (F : C ⥤ D) [IsEquivalence F] : inv (inv F) = F :=
  rfl

variable {E : Type u₃} [Category.{v₃} E]

instance isEquivalenceTrans (F : C ⥤ D) (G : D ⥤ E) [IsEquivalence F] [IsEquivalence G] : IsEquivalence (F ⋙ G) :=
  IsEquivalence.ofEquivalence (Equivalence.trans (asEquivalence F) (asEquivalence G))

end Functor

namespace Equivalenceₓ

@[simp]
theorem functor_inv (E : C ≌ D) : E.Functor.inv = E.inverse :=
  rfl

@[simp]
theorem inverse_inv (E : C ≌ D) : E.inverse.inv = E.Functor :=
  rfl

@[simp]
theorem functor_as_equivalence (E : C ≌ D) : E.Functor.asEquivalence = E := by
  cases E
  congr

@[simp]
theorem inverse_as_equivalence (E : C ≌ D) : E.inverse.asEquivalence = E.symm := by
  cases E
  congr

end Equivalenceₓ

namespace IsEquivalence

@[simp]
theorem fun_inv_map (F : C ⥤ D) [IsEquivalence F] (X Y : D) (f : X ⟶ Y) :
    F.map (F.inv.map f) = F.asEquivalence.counit.app X ≫ f ≫ F.asEquivalence.counitInv.app Y := by
  erw [nat_iso.naturality_2]
  rfl

@[simp]
theorem inv_fun_map (F : C ⥤ D) [IsEquivalence F] (X Y : C) (f : X ⟶ Y) :
    F.inv.map (F.map f) = F.asEquivalence.unitInv.app X ≫ f ≫ F.asEquivalence.Unit.app Y := by
  erw [nat_iso.naturality_1]
  rfl

/-- When a functor `F` is an equivalence of categories, and `G` is isomorphic to `F`, then
`G` is also an equivalence of categories. -/
@[simps]
def ofIso {F G : C ⥤ D} (e : F ≅ G) (hF : IsEquivalence F) : IsEquivalence G where
  inverse := hF.inverse
  unitIso := hF.unitIso ≪≫ NatIso.hcomp e (Iso.refl hF.inverse)
  counitIso := NatIso.hcomp (Iso.refl hF.inverse) e.symm ≪≫ hF.counitIso
  functor_unit_iso_comp' := fun X => by
    dsimp' [← nat_iso.hcomp]
    erw [id_comp, F.map_id, comp_id]
    apply (cancel_epi (e.hom.app X)).mp
    slice_lhs 1 2 => rw [← e.hom.naturality]
    slice_lhs 2 3 => rw [← nat_trans.vcomp_app', e.hom_inv_id]
    simp only [← nat_trans.id_app, ← id_comp, ← comp_id, ← F.map_comp, ← assoc]
    erw [hF.counit_iso.hom.naturality]
    slice_lhs 1 2 => rw [functor_unit_iso_comp]
    simp only [← functor.id_map, ← id_comp]

/-- Compatibility of `of_iso` with the composition of isomorphisms of functors -/
theorem of_iso_trans {F G H : C ⥤ D} (e : F ≅ G) (e' : G ≅ H) (hF : IsEquivalence F) :
    ofIso e' (ofIso e hF) = ofIso (e ≪≫ e') hF := by
  dsimp' [← of_iso]
  congr 1 <;> ext X <;> dsimp' [← nat_iso.hcomp]
  · simp only [← id_comp, ← assoc, ← functor.map_comp]
    
  · simp only [← Functor.map_id, ← comp_id, ← id_comp, ← assoc]
    

/-- Compatibility of `of_iso` with identity isomorphisms of functors -/
theorem of_iso_refl (F : C ⥤ D) (hF : IsEquivalence F) : ofIso (Iso.refl F) hF = hF := by
  rcases hF with ⟨Finv, Funit, Fcounit, Fcomp⟩
  dsimp' [← of_iso]
  congr 1 <;> ext X <;> dsimp' [← nat_iso.hcomp]
  · simp only [← comp_id, ← map_id]
    
  · simp only [← id_comp, ← map_id]
    

/-- When `F` and `G` are two isomorphic functors, then `F` is an equivalence iff `G` is. -/
@[simps]
def equivOfIso {F G : C ⥤ D} (e : F ≅ G) : IsEquivalence F ≃ IsEquivalence G where
  toFun := ofIso e
  invFun := ofIso e.symm
  left_inv := fun hF => by
    rw [of_iso_trans, iso.self_symm_id, of_iso_refl]
  right_inv := fun hF => by
    rw [of_iso_trans, iso.symm_self_id, of_iso_refl]

/-- If `G` and `F ⋙ G` are equivalence of categories, then `F` is also an equivalence. -/
@[simp]
def cancelCompRight {E : Type _} [Category E] (F : C ⥤ D) (G : D ⥤ E) (hG : IsEquivalence G)
    (hGF : IsEquivalence (F ⋙ G)) : IsEquivalence F :=
  ofIso (Functor.associator F G G.inv ≪≫ NatIso.hcomp (Iso.refl F) hG.unitIso.symm ≪≫ rightUnitor F)
    (Functor.isEquivalenceTrans (F ⋙ G) G.inv)

/-- If `F` and `F ⋙ G` are equivalence of categories, then `G` is also an equivalence. -/
@[simp]
def cancelCompLeft {E : Type _} [Category E] (F : C ⥤ D) (G : D ⥤ E) (hF : IsEquivalence F)
    (hGF : IsEquivalence (F ⋙ G)) : IsEquivalence G :=
  ofIso ((Functor.associator F.inv F G).symm ≪≫ NatIso.hcomp hF.counitIso (Iso.refl G) ≪≫ leftUnitor G)
    (Functor.isEquivalenceTrans F.inv (F ⋙ G))

end IsEquivalence

namespace Equivalenceₓ

/-- An equivalence is essentially surjective.

See <https://stacks.math.columbia.edu/tag/02C3>.
-/
theorem ess_surj_of_equivalence (F : C ⥤ D) [IsEquivalence F] : EssSurj F :=
  ⟨fun Y => ⟨F.inv.obj Y, ⟨F.asEquivalence.counitIso.app Y⟩⟩⟩

/-- An equivalence is faithful.

See <https://stacks.math.columbia.edu/tag/02C3>.
-/
-- see Note [lower instance priority]
instance (priority := 100) faithful_of_equivalence (F : C ⥤ D) [IsEquivalence F] :
    Faithful F where map_injective' := fun X Y f g w => by
    have p := congr_arg (@CategoryTheory.Functor.map _ _ _ _ F.inv _ _) w
    simpa only [← cancel_epi, ← cancel_mono, ← is_equivalence.inv_fun_map] using p

/-- An equivalence is full.

See <https://stacks.math.columbia.edu/tag/02C3>.
-/
-- see Note [lower instance priority]
instance (priority := 100) fullOfEquivalence (F : C ⥤ D) [IsEquivalence F] : Full F where
  preimage := fun X Y f => F.asEquivalence.Unit.app X ≫ F.inv.map f ≫ F.asEquivalence.unitInv.app Y
  witness' := fun X Y f =>
    F.inv.map_injective <| by
      simpa only [← is_equivalence.inv_fun_map, ← assoc, ← iso.inv_hom_id_app_assoc, ← iso.inv_hom_id_app] using
        comp_id _

@[simps]
private noncomputable def equivalence_inverse (F : C ⥤ D) [Full F] [Faithful F] [EssSurj F] : D ⥤ C where
  obj := fun X => F.objPreimage X
  map := fun X Y f => F.preimage ((F.objObjPreimageIso X).Hom ≫ f ≫ (F.objObjPreimageIso Y).inv)
  map_id' := fun X => by
    apply F.map_injective
    tidy
  map_comp' := fun X Y Z f g => by
    apply F.map_injective <;> simp

/-- A functor which is full, faithful, and essentially surjective is an equivalence.

See <https://stacks.math.columbia.edu/tag/02C3>.
-/
noncomputable def ofFullyFaithfullyEssSurj (F : C ⥤ D) [Full F] [Faithful F] [EssSurj F] : IsEquivalence F :=
  IsEquivalence.mk (equivalenceInverse F)
    (NatIso.ofComponents (fun X => (F.preimageIso <| F.objObjPreimageIso <| F.obj X).symm) fun X Y f => by
      apply F.map_injective
      run_tac
        obviously)
    (NatIso.ofComponents F.objObjPreimageIso
      (by
        tidy))

@[simp]
theorem functor_map_inj_iff (e : C ≌ D) {X Y : C} (f g : X ⟶ Y) : e.Functor.map f = e.Functor.map g ↔ f = g :=
  ⟨fun h => e.Functor.map_injective h, fun h => h ▸ rfl⟩

@[simp]
theorem inverse_map_inj_iff (e : C ≌ D) {X Y : D} (f g : X ⟶ Y) : e.inverse.map f = e.inverse.map g ↔ f = g :=
  functor_map_inj_iff e.symm f g

instance ess_surj_induced_functor {C' : Type _} (e : C' ≃ D) :
    EssSurj (inducedFunctor e) where mem_ess_image := fun Y =>
    ⟨e.symm Y, by
      simp ⟩

noncomputable instance inducedFunctorOfEquiv {C' : Type _} (e : C' ≃ D) : IsEquivalence (inducedFunctor e) :=
  Equivalence.ofFullyFaithfullyEssSurj _

noncomputable instance fullyFaithfulToEssImage (F : C ⥤ D) [Full F] [Faithful F] : IsEquivalence F.toEssImage :=
  ofFullyFaithfullyEssSurj F.toEssImage

end Equivalenceₓ

end CategoryTheory

