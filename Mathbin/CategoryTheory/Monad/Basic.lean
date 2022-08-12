/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta, Adam Topaz
-/
import Mathbin.CategoryTheory.Functor.Category
import Mathbin.CategoryTheory.Functor.FullyFaithful
import Mathbin.CategoryTheory.Functor.ReflectsIsomorphisms

/-!
# Monads

We construct the categories of monads and comonads, and their forgetful functors to endofunctors.

(Note that these are the category theorist's monads, not the programmers monads.
For the translation, see the file `category_theory.monad.types`.)

For the fact that monads are "just" monoids in the category of endofunctors, see the file
`category_theory.monad.equiv_mon`.
-/


namespace CategoryTheory

open Category

universe v₁ u₁

-- morphism levels before object levels. See note [category_theory universes].
variable (C : Type u₁) [Category.{v₁} C]

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`η'] []
-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`μ'] []
/-- The data of a monad on C consists of an endofunctor T together with natural transformations
η : 𝟭 C ⟶ T and μ : T ⋙ T ⟶ T satisfying three equations:
- T μ_X ≫ μ_X = μ_(TX) ≫ μ_X (associativity)
- η_(TX) ≫ μ_X = 1_X (left unit)
- Tη_X ≫ μ_X = 1_X (right unit)
-/
structure Monad extends C ⥤ C where
  η' : 𝟭 _ ⟶ to_functor
  μ' : to_functor ⋙ to_functor ⟶ to_functor
  assoc' : ∀ X, to_functor.map (NatTrans.app μ' X) ≫ μ'.app _ = μ'.app _ ≫ μ'.app _ := by
    run_tac
      obviously
  left_unit' : ∀ X : C, η'.app (to_functor.obj X) ≫ μ'.app _ = 𝟙 _ := by
    run_tac
      obviously
  right_unit' : ∀ X : C, to_functor.map (η'.app X) ≫ μ'.app _ = 𝟙 _ := by
    run_tac
      obviously

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`ε'] []
-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`δ'] []
/-- The data of a comonad on C consists of an endofunctor G together with natural transformations
ε : G ⟶ 𝟭 C and δ : G ⟶ G ⋙ G satisfying three equations:
- δ_X ≫ G δ_X = δ_X ≫ δ_(GX) (coassociativity)
- δ_X ≫ ε_(GX) = 1_X (left counit)
- δ_X ≫ G ε_X = 1_X (right counit)
-/
structure Comonad extends C ⥤ C where
  ε' : to_functor ⟶ 𝟭 _
  δ' : to_functor ⟶ to_functor ⋙ to_functor
  coassoc' : ∀ X, NatTrans.app δ' _ ≫ to_functor.map (δ'.app X) = δ'.app _ ≫ δ'.app _ := by
    run_tac
      obviously
  left_counit' : ∀ X : C, δ'.app X ≫ ε'.app (to_functor.obj X) = 𝟙 _ := by
    run_tac
      obviously
  right_counit' : ∀ X : C, δ'.app X ≫ to_functor.map (ε'.app X) = 𝟙 _ := by
    run_tac
      obviously

variable {C} (T : Monad C) (G : Comonad C)

instance coeMonad : Coe (Monad C) (C ⥤ C) :=
  ⟨fun T => T.toFunctor⟩

instance coeComonad : Coe (Comonad C) (C ⥤ C) :=
  ⟨fun G => G.toFunctor⟩

@[simp]
theorem monad_to_functor_eq_coe : T.toFunctor = T :=
  rfl

@[simp]
theorem comonad_to_functor_eq_coe : G.toFunctor = G :=
  rfl

/-- The unit for the monad `T`. -/
def Monad.η : 𝟭 _ ⟶ (T : C ⥤ C) :=
  T.η'

/-- The multiplication for the monad `T`. -/
def Monad.μ : (T : C ⥤ C) ⋙ (T : C ⥤ C) ⟶ T :=
  T.μ'

/-- The counit for the comonad `G`. -/
def Comonad.ε : (G : C ⥤ C) ⟶ 𝟭 _ :=
  G.ε'

/-- The comultiplication for the comonad `G`. -/
def Comonad.δ : (G : C ⥤ C) ⟶ (G : C ⥤ C) ⋙ G :=
  G.δ'

/-- A custom simps projection for the functor part of a monad, as a coercion. -/
def Monad.Simps.coe :=
  (T : C ⥤ C)

/-- A custom simps projection for the unit of a monad, in simp normal form. -/
def Monad.Simps.η : 𝟭 _ ⟶ (T : C ⥤ C) :=
  T.η

/-- A custom simps projection for the multiplication of a monad, in simp normal form. -/
def Monad.Simps.μ : (T : C ⥤ C) ⋙ (T : C ⥤ C) ⟶ (T : C ⥤ C) :=
  T.μ

/-- A custom simps projection for the functor part of a comonad, as a coercion. -/
def Comonad.Simps.coe :=
  (G : C ⥤ C)

/-- A custom simps projection for the counit of a comonad, in simp normal form. -/
def Comonad.Simps.ε : (G : C ⥤ C) ⟶ 𝟭 _ :=
  G.ε

/-- A custom simps projection for the comultiplication of a comonad, in simp normal form. -/
def Comonad.Simps.δ : (G : C ⥤ C) ⟶ (G : C ⥤ C) ⋙ (G : C ⥤ C) :=
  G.δ

initialize_simps_projections category_theory.monad (toFunctor → coe, η' → η, μ' → μ)

initialize_simps_projections category_theory.comonad (toFunctor → coe, ε' → ε, δ' → δ)

@[reassoc]
theorem Monad.assoc (T : Monad C) (X : C) : (T : C ⥤ C).map (T.μ.app X) ≫ T.μ.app _ = T.μ.app _ ≫ T.μ.app _ :=
  T.assoc' X

@[simp, reassoc]
theorem Monad.left_unit (T : Monad C) (X : C) : T.η.app ((T : C ⥤ C).obj X) ≫ T.μ.app X = 𝟙 ((T : C ⥤ C).obj X) :=
  T.left_unit' X

@[simp, reassoc]
theorem Monad.right_unit (T : Monad C) (X : C) : (T : C ⥤ C).map (T.η.app X) ≫ T.μ.app X = 𝟙 ((T : C ⥤ C).obj X) :=
  T.right_unit' X

@[reassoc]
theorem Comonad.coassoc (G : Comonad C) (X : C) : G.δ.app _ ≫ (G : C ⥤ C).map (G.δ.app X) = G.δ.app _ ≫ G.δ.app _ :=
  G.coassoc' X

@[simp, reassoc]
theorem Comonad.left_counit (G : Comonad C) (X : C) : G.δ.app X ≫ G.ε.app ((G : C ⥤ C).obj X) = 𝟙 ((G : C ⥤ C).obj X) :=
  G.left_counit' X

@[simp, reassoc]
theorem Comonad.right_counit (G : Comonad C) (X : C) :
    G.δ.app X ≫ (G : C ⥤ C).map (G.ε.app X) = 𝟙 ((G : C ⥤ C).obj X) :=
  G.right_counit' X

/-- A morphism of monads is a natural transformation compatible with η and μ. -/
@[ext]
structure MonadHom (T₁ T₂ : Monad C) extends NatTrans (T₁ : C ⥤ C) T₂ where
  app_η' : ∀ X, T₁.η.app X ≫ app X = T₂.η.app X := by
    run_tac
      obviously
  app_μ' : ∀ X, T₁.μ.app X ≫ app X = ((T₁ : C ⥤ C).map (app X) ≫ app _) ≫ T₂.μ.app X := by
    run_tac
      obviously

/-- A morphism of comonads is a natural transformation compatible with ε and δ. -/
@[ext]
structure ComonadHom (M N : Comonad C) extends NatTrans (M : C ⥤ C) N where
  app_ε' : ∀ X, app X ≫ N.ε.app X = M.ε.app X := by
    run_tac
      obviously
  app_δ' : ∀ X, app X ≫ N.δ.app X = M.δ.app X ≫ app _ ≫ (N : C ⥤ C).map (app X) := by
    run_tac
      obviously

restate_axiom monad_hom.app_η'

restate_axiom monad_hom.app_μ'

attribute [simp, reassoc] monad_hom.app_η monad_hom.app_μ

restate_axiom comonad_hom.app_ε'

restate_axiom comonad_hom.app_δ'

attribute [simp, reassoc] comonad_hom.app_ε comonad_hom.app_δ

instance : Category (Monad C) where
  Hom := MonadHom
  id := fun M => { toNatTrans := 𝟙 (M : C ⥤ C) }
  comp := fun _ _ _ f g => { toNatTrans := { app := fun X => f.app X ≫ g.app X } }

instance : Category (Comonad C) where
  Hom := ComonadHom
  id := fun M => { toNatTrans := 𝟙 (M : C ⥤ C) }
  comp := fun M N L f g => { toNatTrans := { app := fun X => f.app X ≫ g.app X } }

instance {T : Monad C} : Inhabited (MonadHom T T) :=
  ⟨𝟙 T⟩

@[simp]
theorem MonadHom.id_to_nat_trans (T : Monad C) : (𝟙 T : T ⟶ T).toNatTrans = 𝟙 (T : C ⥤ C) :=
  rfl

@[simp]
theorem MonadHom.comp_to_nat_trans {T₁ T₂ T₃ : Monad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    (f ≫ g).toNatTrans = ((f.toNatTrans : _ ⟶ (T₂ : C ⥤ C)) ≫ g.toNatTrans : (T₁ : C ⥤ C) ⟶ T₃) :=
  rfl

instance {G : Comonad C} : Inhabited (ComonadHom G G) :=
  ⟨𝟙 G⟩

@[simp]
theorem ComonadHom.id_to_nat_trans (T : Comonad C) : (𝟙 T : T ⟶ T).toNatTrans = 𝟙 (T : C ⥤ C) :=
  rfl

@[simp]
theorem comp_to_nat_trans {T₁ T₂ T₃ : Comonad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    (f ≫ g).toNatTrans = ((f.toNatTrans : _ ⟶ (T₂ : C ⥤ C)) ≫ g.toNatTrans : (T₁ : C ⥤ C) ⟶ T₃) :=
  rfl

/-- Construct a monad isomorphism from a natural isomorphism of functors where the forward
direction is a monad morphism. -/
@[simps]
def MonadIso.mk {M N : Monad C} (f : (M : C ⥤ C) ≅ N) (f_η f_μ) : M ≅ N where
  Hom := { toNatTrans := f.Hom, app_η' := f_η, app_μ' := f_μ }
  inv :=
    { toNatTrans := f.inv,
      app_η' := fun X => by
        simp [f_η],
      app_μ' := fun X => by
        rw [← nat_iso.cancel_nat_iso_hom_right f]
        simp only [← nat_trans.naturality, ← iso.inv_hom_id_app, ← assoc, ← comp_id, ← f_μ, ←
          nat_trans.naturality_assoc, ← iso.inv_hom_id_app_assoc, functor.map_comp_assoc]
        simp }

/-- Construct a comonad isomorphism from a natural isomorphism of functors where the forward
direction is a comonad morphism. -/
@[simps]
def ComonadIso.mk {M N : Comonad C} (f : (M : C ⥤ C) ≅ N) (f_ε f_δ) : M ≅ N where
  Hom := { toNatTrans := f.Hom, app_ε' := f_ε, app_δ' := f_δ }
  inv :=
    { toNatTrans := f.inv,
      app_ε' := fun X => by
        simp [f_ε],
      app_δ' := fun X => by
        rw [← nat_iso.cancel_nat_iso_hom_left f]
        simp only [← reassoc_of (f_δ X), ← iso.hom_inv_id_app_assoc, ← nat_trans.naturality_assoc]
        rw [← functor.map_comp, iso.hom_inv_id_app, Functor.map_id]
        apply (comp_id _).symm }

variable (C)

/-- The forgetful functor from the category of monads to the category of endofunctors.
-/
@[simps]
def monadToFunctor : Monad C ⥤ C ⥤ C where
  obj := fun T => T
  map := fun M N f => f.toNatTrans

instance : Faithful (monadToFunctor C) where

@[simp]
theorem monad_to_functor_map_iso_monad_iso_mk {M N : Monad C} (f : (M : C ⥤ C) ≅ N) (f_η f_μ) :
    (monadToFunctor _).mapIso (MonadIso.mk f f_η f_μ) = f := by
  ext
  rfl

instance :
    ReflectsIsomorphisms (monadToFunctor C) where reflects := fun M N f i => by
    skip
    convert is_iso.of_iso (monad_iso.mk (as_iso ((monad_to_functor C).map f)) f.app_η f.app_μ)
    ext <;> rfl

/-- The forgetful functor from the category of comonads to the category of endofunctors.
-/
@[simps]
def comonadToFunctor : Comonad C ⥤ C ⥤ C where
  obj := fun G => G
  map := fun M N f => f.toNatTrans

instance : Faithful (comonadToFunctor C) where

@[simp]
theorem comonad_to_functor_map_iso_comonad_iso_mk {M N : Comonad C} (f : (M : C ⥤ C) ≅ N) (f_ε f_δ) :
    (comonadToFunctor _).mapIso (ComonadIso.mk f f_ε f_δ) = f := by
  ext
  rfl

instance :
    ReflectsIsomorphisms (comonadToFunctor C) where reflects := fun M N f i => by
    skip
    convert is_iso.of_iso (comonad_iso.mk (as_iso ((comonad_to_functor C).map f)) f.app_ε f.app_δ)
    ext <;> rfl

variable {C}

/-- An isomorphism of monads gives a natural isomorphism of the underlying functors.
-/
@[simps (config := { rhsMd := semireducible })]
def MonadIso.toNatIso {M N : Monad C} (h : M ≅ N) : (M : C ⥤ C) ≅ N :=
  (monadToFunctor C).mapIso h

/-- An isomorphism of comonads gives a natural isomorphism of the underlying functors.
-/
@[simps (config := { rhsMd := semireducible })]
def ComonadIso.toNatIso {M N : Comonad C} (h : M ≅ N) : (M : C ⥤ C) ≅ N :=
  (comonadToFunctor C).mapIso h

variable (C)

namespace Monadₓ

/-- The identity monad. -/
@[simps]
def id : Monad C where
  toFunctor := 𝟭 C
  η' := 𝟙 (𝟭 C)
  μ' := 𝟙 (𝟭 C)

instance : Inhabited (Monad C) :=
  ⟨Monad.id C⟩

end Monadₓ

namespace Comonad

/-- The identity comonad. -/
@[simps]
def id : Comonad C where
  toFunctor := 𝟭 _
  ε' := 𝟙 (𝟭 C)
  δ' := 𝟙 (𝟭 C)

instance : Inhabited (Comonad C) :=
  ⟨Comonad.id C⟩

end Comonad

end CategoryTheory

