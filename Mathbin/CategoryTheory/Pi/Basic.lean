/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Scott Morrison
-/
import Mathbin.CategoryTheory.NaturalIsomorphism
import Mathbin.CategoryTheory.EqToHom

/-!
# Categories of indexed families of objects.

We define the pointwise category structure on indexed families of objects in a category
(and also the dependent generalization).

-/


namespace CategoryTheory

universe w₀ w₁ w₂ v₁ v₂ u₁ u₂

variable {I : Type w₀} (C : I → Type u₁) [∀ i, Category.{v₁} (C i)]

/-- `pi C` gives the cartesian product of an indexed family of categories.
-/
instance pi : Category.{max w₀ v₁} (∀ i, C i) where
  Hom := fun X Y => ∀ i, X i ⟶ Y i
  id := fun X i => 𝟙 (X i)
  comp := fun X Y Z f g i => f i ≫ g i

/-- This provides some assistance to typeclass search in a common situation,
which otherwise fails. (Without this `category_theory.pi.has_limit_of_has_limit_comp_eval` fails.)
-/
abbrev pi' {I : Type v₁} (C : I → Type u₁) [∀ i, Category.{v₁} (C i)] : Category.{v₁} (∀ i, C i) :=
  CategoryTheory.pi C

attribute [instance] pi'

namespace Pi

@[simp]
theorem id_apply (X : ∀ i, C i) (i) : (𝟙 X : ∀ i, X i ⟶ X i) i = 𝟙 (X i) :=
  rfl

@[simp]
theorem comp_apply {X Y Z : ∀ i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (i) : (f ≫ g : ∀ i, X i ⟶ Z i) i = f i ≫ g i :=
  rfl

/-- The evaluation functor at `i : I`, sending an `I`-indexed family of objects to the object over `i`.
-/
@[simps]
def eval (i : I) : (∀ i, C i) ⥤ C i where
  obj := fun f => f i
  map := fun f g α => α i

section

variable {J : Type w₁}

/-- Pull back an `I`-indexed family of objects to an `J`-indexed family, along a function `J → I`.
-/
@[simps]
def comap (h : J → I) : (∀ i, C i) ⥤ ∀ j, C (h j) where
  obj := fun f i => f (h i)
  map := fun f g α i => α (h i)

variable (I)

/-- The natural isomorphism between
pulling back a grading along the identity function,
and the identity functor. -/
@[simps]
def comapId : comap C (id : I → I) ≅ 𝟭 (∀ i, C i) where
  Hom := { app := fun X => 𝟙 X }
  inv := { app := fun X => 𝟙 X }

variable {I}

variable {K : Type w₂}

/-- The natural isomorphism comparing between
pulling back along two successive functions, and
pulling back along their composition
-/
@[simps]
def comapComp (f : K → J) (g : J → I) : comap C g ⋙ comap (C ∘ g) f ≅ comap C (g ∘ f) where
  Hom := { app := fun X b => 𝟙 (X (g (f b))) }
  inv := { app := fun X b => 𝟙 (X (g (f b))) }

/-- The natural isomorphism between pulling back then evaluating, and just evaluating. -/
@[simps]
def comapEvalIsoEval (h : J → I) (j : J) : comap C h ⋙ eval (C ∘ h) j ≅ eval C (h j) :=
  NatIso.ofComponents (fun f => Iso.refl _)
    (by
      tidy)

end

section

variable {J : Type w₀} {D : J → Type u₁} [∀ j, Category.{v₁} (D j)]

instance sumElimCategoryₓ : ∀ s : Sum I J, Category.{v₁} (Sum.elim C D s)
  | Sum.inl i => by
    dsimp'
    infer_instance
  | Sum.inr j => by
    dsimp'
    infer_instance

/-- The bifunctor combining an `I`-indexed family of objects with a `J`-indexed family of objects
to obtain an `I ⊕ J`-indexed family of objects.
-/
@[simps]
def sum : (∀ i, C i) ⥤ (∀ j, D j) ⥤ ∀ s : Sum I J, Sum.elim C D s where
  obj := fun f => { obj := fun g s => Sum.rec f g s, map := fun g g' α s => Sum.rec (fun i => 𝟙 (f i)) α s }
  map := fun f f' α => { app := fun g s => Sum.rec α (fun j => 𝟙 (g j)) s }

end

variable {C}

/-- An isomorphism between `I`-indexed objects gives an isomorphism between each
pair of corresponding components. -/
@[simps]
def isoApp {X Y : ∀ i, C i} (f : X ≅ Y) (i : I) : X i ≅ Y i :=
  ⟨f.Hom i, f.inv i, by
    dsimp'
    rw [← comp_apply, iso.hom_inv_id, id_apply], by
    dsimp'
    rw [← comp_apply, iso.inv_hom_id, id_apply]⟩

@[simp]
theorem iso_app_refl (X : ∀ i, C i) (i : I) : isoApp (Iso.refl X) i = Iso.refl (X i) :=
  rfl

@[simp]
theorem iso_app_symm {X Y : ∀ i, C i} (f : X ≅ Y) (i : I) : isoApp f.symm i = (isoApp f i).symm :=
  rfl

@[simp]
theorem iso_app_trans {X Y Z : ∀ i, C i} (f : X ≅ Y) (g : Y ≅ Z) (i : I) :
    isoApp (f ≪≫ g) i = isoApp f i ≪≫ isoApp g i :=
  rfl

end Pi

namespace Functor

variable {C}

variable {D : I → Type u₁} [∀ i, Category.{v₁} (D i)] {A : Type u₁} [Category.{u₁} A]

/-- Assemble an `I`-indexed family of functors into a functor between the pi types.
-/
@[simps]
def pi (F : ∀ i, C i ⥤ D i) : (∀ i, C i) ⥤ ∀ i, D i where
  obj := fun f i => (F i).obj (f i)
  map := fun f g α i => (F i).map (α i)

/-- Similar to `pi`, but all functors come from the same category `A`
-/
@[simps]
def pi' (f : ∀ i, A ⥤ C i) : A ⥤ ∀ i, C i where
  obj := fun a i => (f i).obj a
  map := fun a₁ a₂ h i => (f i).map h

section EqToHom

@[simp]
theorem eq_to_hom_proj {x x' : ∀ i, C i} (h : x = x') (i : I) :
    (eqToHom h : x ⟶ x') i = eqToHom (Function.funext_iffₓ.mp h i) := by
  subst h
  rfl

end EqToHom

-- One could add some natural isomorphisms showing
-- how `functor.pi` commutes with `pi.eval` and `pi.comap`.
@[simp]
theorem pi'_eval (f : ∀ i, A ⥤ C i) (i : I) : pi' f ⋙ pi.eval C i = f i := by
  apply Functor.ext <;> intros
  · simp
    
  · rfl
    

/-- Two functors to a product category are equal iff they agree on every coordinate. -/
theorem pi_ext (f f' : A ⥤ ∀ i, C i) (h : ∀ i, f ⋙ pi.eval C i = f' ⋙ pi.eval C i) : f = f' := by
  apply Functor.ext
  swap
  · intro X
    ext i
    specialize h i
    have := congr_obj h X
    simpa
    
  · intro x y p
    ext i
    specialize h i
    have := congr_hom h p
    simpa
    

end Functor

namespace NatTrans

variable {C}

variable {D : I → Type u₁} [∀ i, Category.{v₁} (D i)]

variable {F G : ∀ i, C i ⥤ D i}

/-- Assemble an `I`-indexed family of natural transformations into a single natural transformation.
-/
@[simps]
def pi (α : ∀ i, F i ⟶ G i) : Functor.pi F ⟶ Functor.pi G where app := fun f i => (α i).app (f i)

end NatTrans

end CategoryTheory

