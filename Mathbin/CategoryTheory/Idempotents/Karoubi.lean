/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.CategoryTheory.Idempotents.Basic
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor
import Mathbin.CategoryTheory.Equivalence

/-!
# The Karoubi envelope of a category

In this file, we define the Karoubi envelope `karoubi C` of a category `C`.

## Main constructions and definitions

- `karoubi C` is the Karoubi envelope of a category `C`: it is an idempotent
complete category. It is also preadditive when `C` is preadditive.
- `to_karoubi C : C ⥤ karoubi C` is a fully faithful functor, which is an equivalence
(`to_karoubi_is_equivalence`) when `C` is idempotent complete.

-/


noncomputable section

open CategoryTheory.Category

open CategoryTheory.Preadditive

open CategoryTheory.Limits

open BigOperators

namespace CategoryTheory

variable (C : Type _) [Category C]

namespace Idempotents

/-- In a preadditive category `C`, when an object `X` decomposes as `X ≅ P ⨿ Q`, one may
consider `P` as a direct factor of `X` and up to unique isomorphism, it is determined by the
obvious idempotent `X ⟶ P ⟶ X` which is the projection onto `P` with kernel `Q`. More generally,
one may define a formal direct factor of an object `X : C` : it consists of an idempotent
`p : X ⟶ X` which is thought as the "formal image" of `p`. The type `karoubi C` shall be the
type of the objects of the karoubi enveloppe of `C`. It makes sense for any category `C`. -/
@[nolint has_inhabited_instance]
structure Karoubi where
  x : C
  p : X ⟶ X
  idem : p ≫ p = p

namespace Karoubi

variable {C}

@[ext]
theorem ext {P Q : Karoubi C} (h_X : P.x = Q.x) (h_p : P.p ≫ eqToHom h_X = eqToHom h_X ≫ Q.p) : P = Q := by
  cases P
  cases Q
  dsimp'  at h_X h_p
  subst h_X
  simpa only [← true_andₓ, ← eq_self_iff_true, ← id_comp, ← eq_to_hom_refl, ← heq_iff_eq, ← comp_id] using h_p

/-- A morphism `P ⟶ Q` in the category `karoubi C` is a morphism in the underlying category
`C` which satisfies a relation, which in the preadditive case, expresses that it induces a
map between the corresponding "formal direct factors" and that it vanishes on the complement
formal direct factor. -/
@[ext]
structure Hom (P Q : Karoubi C) where
  f : P.x ⟶ Q.x
  comm : f = P.p ≫ f ≫ Q.p

instance [Preadditive C] (P Q : Karoubi C) : Inhabited (Hom P Q) :=
  ⟨⟨0, by
      rw [zero_comp, comp_zero]⟩⟩

@[simp]
theorem hom_ext {P Q : Karoubi C} {f g : Hom P Q} : f = g ↔ f.f = g.f := by
  constructor
  · intro h
    rw [h]
    
  · ext
    

@[simp, reassoc]
theorem p_comp {P Q : Karoubi C} (f : Hom P Q) : P.p ≫ f.f = f.f := by
  rw [f.comm, ← assoc, P.idem]

@[simp, reassoc]
theorem comp_p {P Q : Karoubi C} (f : Hom P Q) : f.f ≫ Q.p = f.f := by
  rw [f.comm, assoc, assoc, Q.idem]

theorem p_comm {P Q : Karoubi C} (f : Hom P Q) : P.p ≫ f.f = f.f ≫ Q.p := by
  rw [p_comp, comp_p]

theorem comp_proof {P Q R : Karoubi C} (g : Hom Q R) (f : Hom P Q) : f.f ≫ g.f = P.p ≫ (f.f ≫ g.f) ≫ R.p := by
  rw [assoc, comp_p, ← assoc, p_comp]

/-- The category structure on the karoubi envelope of a category. -/
instance : Category (Karoubi C) where
  Hom := Karoubi.Hom
  id := fun P =>
    ⟨P.p, by
      repeat'
        rw [P.idem]⟩
  comp := fun P Q R f g => ⟨f.f ≫ g.f, Karoubi.comp_proof g f⟩

@[simp]
theorem comp {P Q R : Karoubi C} (f : P ⟶ Q) (g : Q ⟶ R) : f ≫ g = ⟨f.f ≫ g.f, comp_proof g f⟩ := by
  rfl

@[simp]
theorem id_eq {P : Karoubi C} :
    𝟙 P =
      ⟨P.p, by
        repeat'
          rw [P.idem]⟩ :=
  by
  rfl

/-- It is possible to coerce an object of `C` into an object of `karoubi C`.
See also the functor `to_karoubi`. -/
instance coe : CoeTₓ C (Karoubi C) :=
  ⟨fun X =>
    ⟨X, 𝟙 X, by
      rw [comp_id]⟩⟩

@[simp]
theorem coe_X (X : C) : (X : Karoubi C).x = X := by
  rfl

@[simp]
theorem coe_p (X : C) : (X : Karoubi C).p = 𝟙 X := by
  rfl

@[simp]
theorem eq_to_hom_f {P Q : Karoubi C} (h : P = Q) : Karoubi.Hom.f (eqToHom h) = P.p ≫ eqToHom (congr_arg Karoubi.x h) :=
  by
  subst h
  simp only [← eq_to_hom_refl, ← karoubi.id_eq, ← comp_id]

end Karoubi

/-- The obvious fully faithful functor `to_karoubi` sends an object `X : C` to the obvious
formal direct factor of `X` given by `𝟙 X`. -/
@[simps]
def toKaroubi : C ⥤ Karoubi C where
  obj := fun X =>
    ⟨X, 𝟙 X, by
      rw [comp_id]⟩
  map := fun X Y f =>
    ⟨f, by
      simp only [← comp_id, ← id_comp]⟩

instance : Full (toKaroubi C) where preimage := fun X Y f => f.f

instance : Faithful (toKaroubi C) where

variable {C}

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
@[simps]
instance [Preadditive C] {P Q : Karoubi C} : AddCommGroupₓ (P ⟶ Q) where
  add := fun f g =>
    ⟨f.f + g.f, by
      rw [add_comp, comp_add]
      congr
      exacts[f.comm, g.comm]⟩
  zero :=
    ⟨0, by
      simp only [← comp_zero, ← zero_comp]⟩
  zero_add := fun f => by
    ext
    simp only [← zero_addₓ]
  add_zero := fun f => by
    ext
    simp only [← add_zeroₓ]
  add_assoc := fun f g h' => by
    simp only [← add_assocₓ]
  add_comm := fun f g => by
    ext
    apply_rules [add_commₓ]
  neg := fun f =>
    ⟨-f.f, by
      simpa only [← neg_comp, ← comp_neg, ← neg_inj] using f.comm⟩
  add_left_neg := fun f => by
    ext
    apply_rules [add_left_negₓ]

namespace Karoubi

theorem hom_eq_zero_iff [Preadditive C] {P Q : Karoubi C} {f : Hom P Q} : f = 0 ↔ f.f = 0 :=
  hom_ext

/-- The map sending `f : P ⟶ Q` to `f.f : P.X ⟶ Q.X` is additive. -/
@[simps]
def inclusionHom [Preadditive C] (P Q : Karoubi C) : AddMonoidHom (P ⟶ Q) (P.x ⟶ Q.x) where
  toFun := fun f => f.f
  map_zero' := rfl
  map_add' := fun f g => rfl

@[simp]
theorem sum_hom [Preadditive C] {P Q : Karoubi C} {α : Type _} (s : Finset α) (f : α → (P ⟶ Q)) :
    (∑ x in s, f x).f = ∑ x in s, (f x).f :=
  AddMonoidHom.map_sum (inclusionHom P Q) f s

end Karoubi

/-- The category `karoubi C` is preadditive if `C` is. -/
instance [Preadditive C] : Preadditive (Karoubi C) where
  homGroup := fun P Q => by
    infer_instance
  add_comp' := fun P Q R f g h => by
    ext
    simp only [← add_comp, ← quiver.hom.add_comm_group_add_f, ← karoubi.comp]
  comp_add' := fun P Q R f g h => by
    ext
    simp only [← comp_add, ← quiver.hom.add_comm_group_add_f, ← karoubi.comp]

instance [Preadditive C] : Functor.Additive (toKaroubi C) where

open Karoubi

variable (C)

instance : IsIdempotentComplete (Karoubi C) := by
  refine' ⟨_⟩
  intro P p hp
  have hp' := hom_ext.mp hp
  simp only [← comp] at hp'
  use ⟨P.X, p.f, hp'⟩
  use
    ⟨p.f, by
      rw [comp_p p, hp']⟩
  use
    ⟨p.f, by
      rw [hp', p_comp p]⟩
  constructor <;> simpa only [← hom_ext] using hp'

instance [IsIdempotentComplete C] : EssSurj (toKaroubi C) :=
  ⟨fun P => by
    have h : is_idempotent_complete C := inferInstance
    rcases is_idempotent_complete.idempotents_split P.X P.p P.idem with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
    use Y
    exact
      Nonempty.intro
        { Hom :=
            ⟨i, by
              erw [id_comp, ← h₂, ← assoc, h₁, id_comp]⟩,
          inv :=
            ⟨e, by
              erw [comp_id, ← h₂, assoc, h₁, comp_id]⟩ }⟩

/-- If `C` is idempotent complete, the functor `to_karoubi : C ⥤ karoubi C` is an equivalence. -/
def toKaroubiIsEquivalence [IsIdempotentComplete C] : IsEquivalence (toKaroubi C) :=
  Equivalence.ofFullyFaithfullyEssSurj (toKaroubi C)

namespace Karoubi

variable {C}

/-- The split mono which appears in the factorisation `decomp_id P`. -/
@[simps]
def decompIdI (P : Karoubi C) : P ⟶ P.x :=
  ⟨P.p, by
    erw [coe_p, comp_id, P.idem]⟩

/-- The split epi which appears in the factorisation `decomp_id P`. -/
@[simps]
def decompIdP (P : Karoubi C) : (P.x : Karoubi C) ⟶ P :=
  ⟨P.p, by
    erw [coe_p, id_comp, P.idem]⟩

/-- The formal direct factor of `P.X` given by the idempotent `P.p` in the category `C`
is actually a direct factor in the category `karoubi C`. -/
theorem decomp_id (P : Karoubi C) : 𝟙 P = decompIdI P ≫ decompIdP P := by
  ext
  simp only [← comp, ← id_eq, ← P.idem, ← decomp_id_i, ← decomp_id_p]

theorem decomp_p (P : Karoubi C) : (toKaroubi C).map P.p = decompIdP P ≫ decompIdI P := by
  ext
  simp only [← comp, ← decomp_id_p_f, ← decomp_id_i_f, ← P.idem, ← to_karoubi_map_f]

theorem decomp_id_i_to_karoubi (X : C) : decompIdI ((toKaroubi C).obj X) = 𝟙 _ := by
  ext
  rfl

theorem decomp_id_p_to_karoubi (X : C) : decompIdP ((toKaroubi C).obj X) = 𝟙 _ := by
  ext
  rfl

theorem decomp_id_i_naturality {P Q : Karoubi C} (f : P ⟶ Q) :
    f ≫ decompIdI _ =
      decompIdI _ ≫
        ⟨f.f, by
          erw [comp_id, id_comp]⟩ :=
  by
  ext
  simp only [← comp, ← decomp_id_i_f, ← karoubi.comp_p, ← karoubi.p_comp]

theorem decomp_id_p_naturality {P Q : Karoubi C} (f : P ⟶ Q) :
    decompIdP P ≫ f =
      (⟨f.f, by
          erw [comp_id, id_comp]⟩ :
          (P.x : Karoubi C) ⟶ Q.x) ≫
        decompIdP Q :=
  by
  ext
  simp only [← comp, ← decomp_id_p_f, ← karoubi.comp_p, ← karoubi.p_comp]

end Karoubi

end Idempotents

end CategoryTheory

