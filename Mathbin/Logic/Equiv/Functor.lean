/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon, Scott Morrison
-/
import Mathbin.Control.Bifunctor
import Mathbin.Logic.Equiv.Basic

/-!
# Functor and bifunctors can be applied to `equiv`s.

We define
```lean
def functor.map_equiv (f : Type u → Type v) [functor f] [is_lawful_functor f] :
  α ≃ β → f α ≃ f β
```
and
```lean
def bifunctor.map_equiv (F : Type u → Type v → Type w) [bifunctor F] [is_lawful_bifunctor F] :
  α ≃ β → α' ≃ β' → F α α' ≃ F β β'
```
-/


universe u v w

variable {α β : Type u}

open Equivₓ

namespace Functor

variable (f : Type u → Type v) [Functor f] [IsLawfulFunctor f]

/-- Apply a functor to an `equiv`. -/
def mapEquiv (h : α ≃ β) : f α ≃ f β where
  toFun := map h
  invFun := map h.symm
  left_inv := fun x => by
    simp [← map_map]
  right_inv := fun x => by
    simp [← map_map]

@[simp]
theorem map_equiv_applyₓ (h : α ≃ β) (x : f α) : (mapEquiv f h : f α ≃ f β) x = map h x :=
  rfl

@[simp]
theorem map_equiv_symm_applyₓ (h : α ≃ β) (y : f β) : (mapEquiv f h : f α ≃ f β).symm y = map h.symm y :=
  rfl

@[simp]
theorem map_equiv_refl : mapEquiv f (Equivₓ.refl α) = Equivₓ.refl (f α) := by
  ext x
  simp only [← map_equiv_apply, ← refl_apply]
  exact IsLawfulFunctor.id_map x

end Functor

namespace Bifunctor

variable {α' β' : Type v} (F : Type u → Type v → Type w) [Bifunctor F] [IsLawfulBifunctor F]

/-- Apply a bifunctor to a pair of `equiv`s. -/
def mapEquiv (h : α ≃ β) (h' : α' ≃ β') : F α α' ≃ F β β' where
  toFun := bimap h h'
  invFun := bimap h.symm h'.symm
  left_inv := fun x => by
    simp [← bimap_bimap, ← id_bimap]
  right_inv := fun x => by
    simp [← bimap_bimap, ← id_bimap]

@[simp]
theorem map_equiv_apply (h : α ≃ β) (h' : α' ≃ β') (x : F α α') :
    (mapEquiv F h h' : F α α' ≃ F β β') x = bimap h h' x :=
  rfl

@[simp]
theorem map_equiv_symm_apply (h : α ≃ β) (h' : α' ≃ β') (y : F β β') :
    (mapEquiv F h h' : F α α' ≃ F β β').symm y = bimap h.symm h'.symm y :=
  rfl

@[simp]
theorem map_equiv_refl_refl : mapEquiv F (Equivₓ.refl α) (Equivₓ.refl α') = Equivₓ.refl (F α α') := by
  ext x
  simp [← id_bimap]

end Bifunctor

