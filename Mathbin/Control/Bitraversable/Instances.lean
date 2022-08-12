/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Control.Bitraversable.Lemmas
import Mathbin.Control.Traversable.Lemmas

/-!
# Bitraversable instances

This file provides `bitraversable` instances for concrete bifunctors:
* `prod`
* `sum`
* `functor.const`
* `flip`
* `function.bicompl`
* `function.bicompr`

## References

* Hackage: <https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Bitraversable.html>

## Tags

traversable bitraversable functor bifunctor applicative
-/


universe u v w

variable {t : Type u → Type u → Type u} [Bitraversable t]

section

variable {F : Type u → Type u} [Applicativeₓ F]

/-- The bitraverse function for `α × β`. -/
def Prod.bitraverseₓ {α α' β β'} (f : α → F α') (f' : β → F β') : α × β → F (α' × β')
  | (x, y) => Prod.mk <$> f x <*> f' y

instance : Bitraversable Prod where bitraverse := @Prod.bitraverseₓ

instance : IsLawfulBitraversable Prod := by
  constructor <;> intros <;> cases x <;> simp' [← bitraverse, ← Prod.bitraverseₓ] with functor_norm <;> rfl

open Functor

/-- The bitraverse function for `α ⊕ β`. -/
def Sum.bitraverseₓ {α α' β β'} (f : α → F α') (f' : β → F β') : Sum α β → F (Sum α' β')
  | Sum.inl x => Sum.inl <$> f x
  | Sum.inr x => Sum.inr <$> f' x

instance : Bitraversable Sum where bitraverse := @Sum.bitraverseₓ

instance : IsLawfulBitraversable Sum := by
  constructor <;> intros <;> cases x <;> simp' [← bitraverse, ← Sum.bitraverseₓ] with functor_norm <;> rfl

/-- The bitraverse function for `const`. It throws away the second map. -/
@[nolint unused_arguments]
def Const.bitraverse {α α' β β'} (f : α → F α') (f' : β → F β') : Const α β → F (Const α' β') :=
  f

instance Bitraversable.const : Bitraversable Const where bitraverse := @Const.bitraverse

instance IsLawfulBitraversable.const : IsLawfulBitraversable Const := by
  constructor <;> intros <;> simp' [← bitraverse, ← Const.bitraverse] with functor_norm <;> rfl

/-- The bitraverse function for `flip`. -/
def flip.bitraverse {α α' β β'} (f : α → F α') (f' : β → F β') : flip t α β → F (flip t α' β') :=
  (bitraverse f' f : t β α → F (t β' α'))

instance Bitraversable.flip : Bitraversable (flip t) where bitraverse := @flip.bitraverse t _

open IsLawfulBitraversable

instance IsLawfulBitraversable.flip [IsLawfulBitraversable t] : IsLawfulBitraversable (flip t) := by
  constructor <;>
    intros <;>
      casesm IsLawfulBitraversable t <;>
        run_tac
          tactic.apply_assumption

open Bitraversable Functor

instance (priority := 10) Bitraversable.traversable {α} : Traversable (t α) where traverse := @tsnd t _ _

instance (priority := 10) Bitraversable.isLawfulTraversable [IsLawfulBitraversable t] {α} : IsLawfulTraversable (t α) :=
  by
  constructor <;> intros <;> simp' [← traverse, ← comp_tsnd] with functor_norm
  · rfl
    
  · simp [← tsnd_eq_snd_id]
    rfl
    
  · simp' [← tsnd, ← binaturality, ← Function.comp] with functor_norm
    

end

open Bifunctor Traversable IsLawfulTraversable IsLawfulBitraversable

open Function (bicompl bicompr)

section Bicompl

variable (F G : Type u → Type u) [Traversable F] [Traversable G]

/-- The bitraverse function for `bicompl`. -/
def Bicompl.bitraverse {m} [Applicativeₓ m] {α β α' β'} (f : α → m β) (f' : α' → m β') :
    bicompl t F G α α' → m (bicompl t F G β β') :=
  (bitraverse (traverse f) (traverse f') : t (F α) (G α') → m _)

instance : Bitraversable (bicompl t F G) where bitraverse := @Bicompl.bitraverse t _ F G _ _

instance [IsLawfulTraversable F] [IsLawfulTraversable G] [IsLawfulBitraversable t] :
    IsLawfulBitraversable (bicompl t F G) := by
  constructor <;>
    intros <;>
      simp' [← bitraverse, ← Bicompl.bitraverse, ← bimap, ← traverse_id, ← bitraverse_id_id, ← comp_bitraverse] with
        functor_norm
  · simp [← traverse_eq_map_id', ← bitraverse_eq_bimap_id]
    
  · revert x
    dunfold bicompl
    simp [← binaturality, ← naturality_pf]
    

end Bicompl

section Bicompr

variable (F : Type u → Type u) [Traversable F]

/-- The bitraverse function for `bicompr`. -/
def Bicompr.bitraverse {m} [Applicativeₓ m] {α β α' β'} (f : α → m β) (f' : α' → m β') :
    bicompr F t α α' → m (bicompr F t β β') :=
  (traverse (bitraverse f f') : F (t α α') → m _)

instance : Bitraversable (bicompr F t) where bitraverse := @Bicompr.bitraverse t _ F _

instance [IsLawfulTraversable F] [IsLawfulBitraversable t] : IsLawfulBitraversable (bicompr F t) := by
  constructor <;> intros <;> simp' [← bitraverse, ← Bicompr.bitraverse, ← bitraverse_id_id] with functor_norm
  · simp [← bitraverse_eq_bimap_id', ← traverse_eq_map_id']
    rfl
    
  · revert x
    dunfold bicompr
    intro
    simp [← naturality, ← binaturality']
    

end Bicompr

