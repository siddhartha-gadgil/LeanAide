/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Scott Morrison
-/
import Mathbin.CategoryTheory.Subobject.MonoOver
import Mathbin.CategoryTheory.Skeletal
import Mathbin.Tactic.Elementwise
import Mathbin.Tactic.ApplyFun

/-!
# Subobjects

We define `subobject X` as the quotient (by isomorphisms) of
`mono_over X := {f : over X // mono f.hom}`.

Here `mono_over X` is a thin category (a pair of objects has at most one morphism between them),
so we can think of it as a preorder. However as it is not skeletal, it is not a partial order.

There is a coercion from `subobject X` back to the ambient category `C`
(using choice to pick a representative), and for `P : subobject X`,
`P.arrow : (P : C) ⟶ X` is the inclusion morphism.

We provide
* `def pullback [has_pullbacks C] (f : X ⟶ Y) : subobject Y ⥤ subobject X`
* `def map (f : X ⟶ Y) [mono f] : subobject X ⥤ subobject Y`
* `def «exists» [has_images C] (f : X ⟶ Y) : subobject X ⥤ subobject Y`
and prove their basic properties and relationships.
These are all easy consequences of the earlier development
of the corresponding functors for `mono_over`.

The subobjects of `X` form a preorder making them into a category. We have `X ≤ Y` if and only if
`X.arrow` factors through `Y.arrow`: see `of_le`/`of_le_mk`/`of_mk_le`/`of_mk_le_mk` and
`le_of_comm`. Similarly, to show that two subobjects are equal, we can supply an isomorphism between
the underlying objects that commutes with the arrows (`eq_of_comm`).

See also

* `category_theory.subobject.factor_thru` :
  an API describing factorization of morphisms through subobjects.
* `category_theory.subobject.lattice` :
  the lattice structures on subobjects.

## Notes

This development originally appeared in Bhavik Mehta's "Topos theory for Lean" repository,
and was ported to mathlib by Scott Morrison.

### Implementation note

Currently we describe `pullback`, `map`, etc., as functors.
It may be better to just say that they are monotone functions,
and even avoid using categorical language entirely when describing `subobject X`.
(It's worth keeping this in mind in future use; it should be a relatively easy change here
if it looks preferable.)

### Relation to pseudoelements

There is a separate development of pseudoelements in `category_theory.abelian.pseudoelements`,
as a quotient (but not by isomorphism) of `over X`.

When a morphism `f` has an image, the image represents the same pseudoelement.
In a category with images `pseudoelements X` could be constructed as a quotient of `mono_over X`.
In fact, in an abelian category (I'm not sure in what generality beyond that),
`pseudoelements X` agrees with `subobject X`, but we haven't developed this in mathlib yet.

-/


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}

variable {D : Type u₂} [Category.{v₂} D]

/-!
We now construct the subobject lattice for `X : C`,
as the quotient by isomorphisms of `mono_over X`.

Since `mono_over X` is a thin category, we use `thin_skeleton` to take the quotient.

Essentially all the structure defined above on `mono_over X` descends to `subobject X`,
with morphisms becoming inequalities, and isomorphisms becoming equations.
-/


/-- The category of subobjects of `X : C`, defined as isomorphism classes of monomorphisms into `X`.
-/
def Subobject (X : C) :=
  ThinSkeleton (MonoOver X)deriving PartialOrderₓ, Category

namespace Subobject

/-- Convenience constructor for a subobject. -/
abbrev mk {X A : C} (f : A ⟶ X) [Mono f] : Subobject X :=
  (toThinSkeleton _).obj (MonoOver.mk' f)

/-- The category of subobjects is equivalent to the `mono_over` category. It is more convenient to
use the former due to the partial order instance, but oftentimes it is easier to define structures
on the latter. -/
noncomputable def equivMonoOver (X : C) : Subobject X ≌ MonoOver X :=
  ThinSkeleton.equivalence _

/-- Use choice to pick a representative `mono_over X` for each `subobject X`.
-/
noncomputable def representative {X : C} : Subobject X ⥤ MonoOver X :=
  (equivMonoOver X).Functor

/-- Starting with `A : mono_over X`, we can take its equivalence class in `subobject X`
then pick an arbitrary representative using `representative.obj`.
This is isomorphic (in `mono_over X`) to the original `A`.
-/
noncomputable def representativeIso {X : C} (A : MonoOver X) : representative.obj ((toThinSkeleton _).obj A) ≅ A :=
  (equivMonoOver X).counitIso.app A

/-- Use choice to pick a representative underlying object in `C` for any `subobject X`.

Prefer to use the coercion `P : C` rather than explicitly writing `underlying.obj P`.
-/
noncomputable def underlying {X : C} : Subobject X ⥤ C :=
  representative ⋙ MonoOver.forget _ ⋙ Over.forget _

instance : Coe (Subobject X) C where coe := fun Y => underlying.obj Y

@[simp]
theorem underlying_as_coe {X : C} (P : Subobject X) : underlying.obj P = P :=
  rfl

/-- If we construct a `subobject Y` from an explicit `f : X ⟶ Y` with `[mono f]`,
then pick an arbitrary choice of underlying object `(subobject.mk f : C)` back in `C`,
it is isomorphic (in `C`) to the original `X`.
-/
noncomputable def underlyingIso {X Y : C} (f : X ⟶ Y) [Mono f] : (Subobject.mk f : C) ≅ X :=
  (MonoOver.forget _ ⋙ Over.forget _).mapIso (representativeIso (MonoOver.mk' f))

/-- The morphism in `C` from the arbitrarily chosen underlying object to the ambient object.
-/
noncomputable def arrow {X : C} (Y : Subobject X) : (Y : C) ⟶ X :=
  (representative.obj Y).val.Hom

instance arrow_mono {X : C} (Y : Subobject X) : Mono Y.arrow :=
  (representative.obj Y).property

@[simp]
theorem arrow_congr {A : C} (X Y : Subobject A) (h : X = Y) :
    eqToHom (congr_arg (fun X : Subobject A => (X : C)) h) ≫ Y.arrow = X.arrow := by
  induction h
  simp

@[simp]
theorem representative_coe (Y : Subobject X) : (representative.obj Y : C) = (Y : C) :=
  rfl

@[simp]
theorem representative_arrow (Y : Subobject X) : (representative.obj Y).arrow = Y.arrow :=
  rfl

@[simp, reassoc]
theorem underlying_arrow {X : C} {Y Z : Subobject X} (f : Y ⟶ Z) : underlying.map f ≫ arrow Z = arrow Y :=
  Over.w (representative.map f)

@[simp, reassoc, elementwise]
theorem underlying_iso_arrow {X Y : C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f :=
  Over.w _

@[simp, reassoc]
theorem underlying_iso_hom_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).Hom ≫ f = (mk f).arrow :=
  (Iso.eq_inv_comp _).1 (underlying_iso_arrow f).symm

/-- Two morphisms into a subobject are equal exactly if
the morphisms into the ambient object are equal -/
@[ext]
theorem eq_of_comp_arrow_eq {X Y : C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g :=
  (cancel_mono P.arrow).mp h

theorem mk_le_mk_of_comm {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂) (w : g ≫ f₂ = f₁) :
    mk f₁ ≤ mk f₂ :=
  ⟨MonoOver.homMk _ w⟩

@[simp]
theorem mk_arrow (P : Subobject X) : mk P.arrow = P :=
  (Quotientₓ.induction_on' P) fun Q => by
    obtain ⟨e⟩ := @Quotientₓ.mk_out' _ (is_isomorphic_setoid _) Q
    refine' Quotientₓ.sound' ⟨mono_over.iso_mk _ _ ≪≫ e⟩ <;> tidy

theorem le_of_comm {B : C} {X Y : Subobject B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow) : X ≤ Y := by
  convert mk_le_mk_of_comm _ w <;> simp

theorem le_mk_of_comm {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (g : (X : C) ⟶ A) (w : g ≫ f = X.arrow) :
    X ≤ mk f :=
  le_of_comm (g ≫ (underlyingIso f).inv) <| by
    simp [← w]

theorem mk_le_of_comm {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (g : A ⟶ (X : C)) (w : g ≫ X.arrow = f) :
    mk f ≤ X :=
  le_of_comm ((underlyingIso f).Hom ≫ g) <| by
    simp [← w]

/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
    the arrows. -/
@[ext]
theorem eq_of_comm {B : C} {X Y : Subobject B} (f : (X : C) ≅ (Y : C)) (w : f.Hom ≫ Y.arrow = X.arrow) : X = Y :=
  le_antisymmₓ (le_of_comm f.Hom w) <| le_of_comm f.inv <| f.inv_comp_eq.2 w.symm

/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
    the arrows. -/
@[ext]
theorem eq_mk_of_comm {B A : C} {X : Subobject B} (f : A ⟶ B) [Mono f] (i : (X : C) ≅ A) (w : i.Hom ≫ f = X.arrow) :
    X = mk f :=
  eq_of_comm (i.trans (underlyingIso f).symm) <| by
    simp [← w]

/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
    the arrows. -/
@[ext]
theorem mk_eq_of_comm {B A : C} {X : Subobject B} (f : A ⟶ B) [Mono f] (i : A ≅ (X : C)) (w : i.Hom ≫ X.arrow = f) :
    mk f = X :=
  Eq.symm <|
    eq_mk_of_comm _ i.symm <| by
      rw [iso.symm_hom, iso.inv_comp_eq, w]

/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
    the arrows. -/
@[ext]
theorem mk_eq_mk_of_comm {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (i : A₁ ≅ A₂) (w : i.Hom ≫ g = f) :
    mk f = mk g :=
  eq_mk_of_comm _ ((underlyingIso f).trans i) <| by
    simp [← w]

/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
-- We make `X` and `Y` explicit arguments here so that when `of_le` appears in goal statements
-- it is possible to see its source and target
-- (`h` will just display as `_`, because it is in `Prop`).
def ofLe {B : C} (X Y : Subobject B) (h : X ≤ Y) : (X : C) ⟶ (Y : C) :=
  underlying.map <| h.Hom

@[simp, reassoc]
theorem of_le_arrow {B : C} {X Y : Subobject B} (h : X ≤ Y) : ofLe X Y h ≫ Y.arrow = X.arrow :=
  underlying_arrow _

instance {B : C} (X Y : Subobject B) (h : X ≤ Y) : Mono (ofLe X Y h) := by
  fconstructor
  intro Z f g w
  replace w := w =≫ Y.arrow
  ext
  simpa using w

theorem of_le_mk_le_mk_of_comm {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂)
    (w : g ≫ f₂ = f₁) : ofLe _ _ (mk_le_mk_of_comm g w) = (underlyingIso _).Hom ≫ g ≫ (underlyingIso _).inv := by
  ext
  simp [← w]

/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
def ofLeMk {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X ≤ mk f) : (X : C) ⟶ A :=
  ofLe X (mk f) h ≫ (underlyingIso f).Hom deriving Mono

@[simp]
theorem of_le_mk_comp {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (h : X ≤ mk f) : ofLeMk X f h ≫ f = X.arrow := by
  simp [← of_le_mk]

/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
def ofMkLe {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f ≤ X) : A ⟶ (X : C) :=
  (underlyingIso f).inv ≫ ofLe (mk f) X h deriving Mono

@[simp]
theorem of_mk_le_arrow {B A : C} {f : A ⟶ B} [Mono f] {X : Subobject B} (h : mk f ≤ X) : ofMkLe f X h ≫ X.arrow = f :=
  by
  simp [← of_mk_le]

/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
def ofMkLeMk {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f ≤ mk g) : A₁ ⟶ A₂ :=
  (underlyingIso f).inv ≫ ofLe (mk f) (mk g) h ≫ (underlyingIso g).Hom deriving Mono

@[simp]
theorem of_mk_le_mk_comp {B A₁ A₂ : C} {f : A₁ ⟶ B} {g : A₂ ⟶ B} [Mono f] [Mono g] (h : mk f ≤ mk g) :
    ofMkLeMk f g h ≫ g = f := by
  simp [← of_mk_le_mk]

@[simp, reassoc]
theorem of_le_comp_of_le {B : C} (X Y Z : Subobject B) (h₁ : X ≤ Y) (h₂ : Y ≤ Z) :
    ofLe X Y h₁ ≫ ofLe Y Z h₂ = ofLe X Z (h₁.trans h₂) := by
  simp [← of_le, functor.map_comp underlying]

@[simp, reassoc]
theorem of_le_comp_of_le_mk {B A : C} (X Y : Subobject B) (f : A ⟶ B) [Mono f] (h₁ : X ≤ Y) (h₂ : Y ≤ mk f) :
    ofLe X Y h₁ ≫ ofLeMk Y f h₂ = ofLeMk X f (h₁.trans h₂) := by
  simp [← of_mk_le, ← of_le_mk, ← of_le, functor.map_comp_assoc underlying]

@[simp, reassoc]
theorem of_le_mk_comp_of_mk_le {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (Y : Subobject B) (h₁ : X ≤ mk f)
    (h₂ : mk f ≤ Y) : ofLeMk X f h₁ ≫ ofMkLe f Y h₂ = ofLe X Y (h₁.trans h₂) := by
  simp [← of_mk_le, ← of_le_mk, ← of_le, functor.map_comp underlying]

@[simp, reassoc]
theorem of_le_mk_comp_of_mk_le_mk {B A₁ A₂ : C} (X : Subobject B) (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B) [Mono g]
    (h₁ : X ≤ mk f) (h₂ : mk f ≤ mk g) : ofLeMk X f h₁ ≫ ofMkLeMk f g h₂ = ofLeMk X g (h₁.trans h₂) := by
  simp [← of_mk_le, ← of_le_mk, ← of_le, ← of_mk_le_mk, functor.map_comp_assoc underlying]

@[simp, reassoc]
theorem of_mk_le_comp_of_le {B A₁ : C} (f : A₁ ⟶ B) [Mono f] (X Y : Subobject B) (h₁ : mk f ≤ X) (h₂ : X ≤ Y) :
    ofMkLe f X h₁ ≫ ofLe X Y h₂ = ofMkLe f Y (h₁.trans h₂) := by
  simp [← of_mk_le, ← of_le_mk, ← of_le, ← of_mk_le_mk, functor.map_comp underlying]

@[simp, reassoc]
theorem of_mk_le_comp_of_le_mk {B A₁ A₂ : C} (f : A₁ ⟶ B) [Mono f] (X : Subobject B) (g : A₂ ⟶ B) [Mono g]
    (h₁ : mk f ≤ X) (h₂ : X ≤ mk g) : ofMkLe f X h₁ ≫ ofLeMk X g h₂ = ofMkLeMk f g (h₁.trans h₂) := by
  simp [← of_mk_le, ← of_le_mk, ← of_le, ← of_mk_le_mk, functor.map_comp_assoc underlying]

@[simp, reassoc]
theorem of_mk_le_mk_comp_of_mk_le {B A₁ A₂ : C} (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B) [Mono g] (X : Subobject B)
    (h₁ : mk f ≤ mk g) (h₂ : mk g ≤ X) : ofMkLeMk f g h₁ ≫ ofMkLe g X h₂ = ofMkLe f X (h₁.trans h₂) := by
  simp [← of_mk_le, ← of_le_mk, ← of_le, ← of_mk_le_mk, functor.map_comp underlying]

@[simp, reassoc]
theorem of_mk_le_mk_comp_of_mk_le_mk {B A₁ A₂ A₃ : C} (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B) [Mono g] (h : A₃ ⟶ B) [Mono h]
    (h₁ : mk f ≤ mk g) (h₂ : mk g ≤ mk h) : ofMkLeMk f g h₁ ≫ ofMkLeMk g h h₂ = ofMkLeMk f h (h₁.trans h₂) := by
  simp [← of_mk_le, ← of_le_mk, ← of_le, ← of_mk_le_mk, functor.map_comp_assoc underlying]

@[simp]
theorem of_le_refl {B : C} (X : Subobject B) : ofLe X X le_rfl = 𝟙 _ := by
  apply (cancel_mono X.arrow).mp
  simp

@[simp]
theorem of_mk_le_mk_refl {B A₁ : C} (f : A₁ ⟶ B) [Mono f] : ofMkLeMk f f le_rfl = 𝟙 _ := by
  apply (cancel_mono f).mp
  simp

/-- An equality of subobjects gives an isomorphism of the corresponding objects.
(One could use `underlying.map_iso (eq_to_iso h))` here, but this is more readable.) -/
-- As with `of_le`, we have `X` and `Y` as explicit arguments for readability.
@[simps]
def isoOfEq {B : C} (X Y : Subobject B) (h : X = Y) : (X : C) ≅ (Y : C) where
  Hom := ofLe _ _ h.le
  inv := ofLe _ _ h.Ge

/-- An equality of subobjects gives an isomorphism of the corresponding objects. -/
@[simps]
def isoOfEqMk {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X = mk f) : (X : C) ≅ A where
  Hom := ofLeMk X f h.le
  inv := ofMkLe f X h.Ge

/-- An equality of subobjects gives an isomorphism of the corresponding objects. -/
@[simps]
def isoOfMkEq {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f = X) : A ≅ (X : C) where
  Hom := ofMkLe f X h.le
  inv := ofLeMk X f h.Ge

/-- An equality of subobjects gives an isomorphism of the corresponding objects. -/
@[simps]
def isoOfMkEqMk {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f = mk g) : A₁ ≅ A₂ where
  Hom := ofMkLeMk f g h.le
  inv := ofMkLeMk g f h.Ge

end Subobject

open CategoryTheory.Limits

namespace Subobject

/-- Any functor `mono_over X ⥤ mono_over Y` descends to a functor
`subobject X ⥤ subobject Y`, because `mono_over Y` is thin. -/
def lower {Y : D} (F : MonoOver X ⥤ MonoOver Y) : Subobject X ⥤ Subobject Y :=
  ThinSkeleton.map F

/-- Isomorphic functors become equal when lowered to `subobject`.
(It's not as evil as usual to talk about equality between functors
because the categories are thin and skeletal.) -/
theorem lower_iso (F₁ F₂ : MonoOver X ⥤ MonoOver Y) (h : F₁ ≅ F₂) : lower F₁ = lower F₂ :=
  ThinSkeleton.map_iso_eq h

/-- A ternary version of `subobject.lower`. -/
def lower₂ (F : MonoOver X ⥤ MonoOver Y ⥤ MonoOver Z) : Subobject X ⥤ Subobject Y ⥤ Subobject Z :=
  ThinSkeleton.map₂ F

@[simp]
theorem lower_comm (F : MonoOver Y ⥤ MonoOver X) : toThinSkeleton _ ⋙ lower F = F ⋙ toThinSkeleton _ :=
  rfl

/-- An adjunction between `mono_over A` and `mono_over B` gives an adjunction
between `subobject A` and `subobject B`. -/
def lowerAdjunction {A : C} {B : D} {L : MonoOver A ⥤ MonoOver B} {R : MonoOver B ⥤ MonoOver A} (h : L ⊣ R) :
    lower L ⊣ lower R :=
  ThinSkeleton.lowerAdjunction _ _ h

/-- An equivalence between `mono_over A` and `mono_over B` gives an equivalence
between `subobject A` and `subobject B`. -/
@[simps]
def lowerEquivalence {A : C} {B : D} (e : MonoOver A ≌ MonoOver B) : Subobject A ≌ Subobject B where
  Functor := lower e.Functor
  inverse := lower e.inverse
  unitIso := by
    apply eq_to_iso
    convert thin_skeleton.map_iso_eq e.unit_iso
    · exact thin_skeleton.map_id_eq.symm
      
    · exact (thin_skeleton.map_comp_eq _ _).symm
      
  counitIso := by
    apply eq_to_iso
    convert thin_skeleton.map_iso_eq e.counit_iso
    · exact (thin_skeleton.map_comp_eq _ _).symm
      
    · exact thin_skeleton.map_id_eq.symm
      

section Pullback

variable [HasPullbacks C]

/-- When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `subobject Y ⥤ subobject X`,
by pulling back a monomorphism along `f`. -/
def pullback (f : X ⟶ Y) : Subobject Y ⥤ Subobject X :=
  lower (MonoOver.pullback f)

theorem pullback_id (x : Subobject X) : (pullback (𝟙 X)).obj x = x := by
  apply Quotientₓ.induction_on' x
  intro f
  apply Quotientₓ.sound
  exact ⟨mono_over.pullback_id.app f⟩

theorem pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : Subobject Z) :
    (pullback (f ≫ g)).obj x = (pullback f).obj ((pullback g).obj x) := by
  apply Quotientₓ.induction_on' x
  intro t
  apply Quotientₓ.sound
  refine' ⟨(mono_over.pullback_comp _ _).app t⟩

instance (f : X ⟶ Y) : Faithful (pullback f) where

end Pullback

section Map

/-- We can map subobjects of `X` to subobjects of `Y`
by post-composition with a monomorphism `f : X ⟶ Y`.
-/
def map (f : X ⟶ Y) [Mono f] : Subobject X ⥤ Subobject Y :=
  lower (MonoOver.map f)

theorem map_id (x : Subobject X) : (map (𝟙 X)).obj x = x := by
  apply Quotientₓ.induction_on' x
  intro f
  apply Quotientₓ.sound
  exact ⟨mono_over.map_id.app f⟩

theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] (x : Subobject X) :
    (map (f ≫ g)).obj x = (map g).obj ((map f).obj x) := by
  apply Quotientₓ.induction_on' x
  intro t
  apply Quotientₓ.sound
  refine' ⟨(mono_over.map_comp _ _).app t⟩

/-- Isomorphic objects have equivalent subobject lattices. -/
def mapIso {A B : C} (e : A ≅ B) : Subobject A ≌ Subobject B :=
  lowerEquivalence (MonoOver.mapIso e)

/-- In fact, there's a type level bijection between the subobjects of isomorphic objects,
which preserves the order. -/
-- @[simps] here generates a lemma `map_iso_to_order_iso_to_equiv_symm_apply`
-- whose left hand side is not in simp normal form.
def mapIsoToOrderIso (e : X ≅ Y) : Subobject X ≃o Subobject Y where
  toFun := (map e.Hom).obj
  invFun := (map e.inv).obj
  left_inv := fun g => by
    simp_rw [← map_comp, e.hom_inv_id, map_id]
  right_inv := fun g => by
    simp_rw [← map_comp, e.inv_hom_id, map_id]
  map_rel_iff' := fun A B => by
    dsimp'
    fconstructor
    · intro h
      apply_fun (map e.inv).obj  at h
      simp_rw [← map_comp, e.hom_inv_id, map_id] at h
      exact h
      
    · intro h
      apply_fun (map e.hom).obj  at h
      exact h
      

@[simp]
theorem map_iso_to_order_iso_apply (e : X ≅ Y) (P : Subobject X) : mapIsoToOrderIso e P = (map e.Hom).obj P :=
  rfl

@[simp]
theorem map_iso_to_order_iso_symm_apply (e : X ≅ Y) (Q : Subobject Y) :
    (mapIsoToOrderIso e).symm Q = (map e.inv).obj Q :=
  rfl

/-- `map f : subobject X ⥤ subobject Y` is
the left adjoint of `pullback f : subobject Y ⥤ subobject X`. -/
def mapPullbackAdj [HasPullbacks C] (f : X ⟶ Y) [Mono f] : map f ⊣ pullback f :=
  lowerAdjunction (MonoOver.mapPullbackAdj f)

@[simp]
theorem pullback_map_self [HasPullbacks C] (f : X ⟶ Y) [Mono f] (g : Subobject X) :
    (pullback f).obj ((map f).obj g) = g := by
  revert g
  apply Quotientₓ.ind
  intro g'
  apply Quotientₓ.sound
  exact ⟨(mono_over.pullback_map_self f).app _⟩

theorem map_pullback [HasPullbacks C] {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} [Mono h] [Mono g]
    (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk f g comm)) (p : Subobject Y) :
    (map g).obj ((pullback f).obj p) = (pullback k).obj ((map h).obj p) := by
  revert p
  apply Quotientₓ.ind'
  intro a
  apply Quotientₓ.sound
  apply thin_skeleton.equiv_of_both_ways
  · refine' mono_over.hom_mk (pullback.lift pullback.fst _ _) (pullback.lift_snd _ _ _)
    change _ ≫ a.arrow ≫ h = (pullback.snd ≫ g) ≫ _
    rw [assoc, ← comm, pullback.condition_assoc]
    
  · refine'
      mono_over.hom_mk
        (pullback.lift pullback.fst (pullback_cone.is_limit.lift' t (pullback.fst ≫ a.arrow) pullback.snd _).1
          (pullback_cone.is_limit.lift' _ _ _ _).2.1.symm)
        _
    · rw [← pullback.condition, assoc]
      rfl
      
    · dsimp'
      rw [pullback.lift_snd_assoc]
      apply (pullback_cone.is_limit.lift' _ _ _ _).2.2
      
    

end Map

section Exists

variable [HasImages C]

/-- The functor from subobjects of `X` to subobjects of `Y` given by
sending the subobject `S` to its "image" under `f`, usually denoted $\exists_f$.
For instance, when `C` is the category of types,
viewing `subobject X` as `set X` this is just `set.image f`.

This functor is left adjoint to the `pullback f` functor (shown in `exists_pullback_adj`)
provided both are defined, and generalises the `map f` functor, again provided it is defined.
-/
def exists (f : X ⟶ Y) : Subobject X ⥤ Subobject Y :=
  lower (MonoOver.exists f)

/-- When `f : X ⟶ Y` is a monomorphism, `exists f` agrees with `map f`.
-/
theorem exists_iso_map (f : X ⟶ Y) [Mono f] : exists f = map f :=
  lower_iso _ _ (MonoOver.existsIsoMap f)

/-- `exists f : subobject X ⥤ subobject Y` is
left adjoint to `pullback f : subobject Y ⥤ subobject X`.
-/
def existsPullbackAdj (f : X ⟶ Y) [HasPullbacks C] : exists f ⊣ pullback f :=
  lowerAdjunction (MonoOver.existsPullbackAdj f)

end Exists

end Subobject

end CategoryTheory

