/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Logic.Equiv.Basic

/-!
# Functions functorial with respect to equivalences

An `equiv_functor` is a function from `Type → Type` equipped with the additional data of
coherently mapping equivalences to equivalences.

In categorical language, it is an endofunctor of the "core" of the category `Type`.
-/


universe u₀ u₁ u₂ v₀ v₁ v₂

open Function

/-- An `equiv_functor` is only functorial with respect to equivalences.

To construct an `equiv_functor`, it suffices to supply just the function `f α → f β` from
an equivalence `α ≃ β`, and then prove the functor laws. It's then a consequence that
this function is part of an equivalence, provided by `equiv_functor.map_equiv`.
-/
class EquivFunctor (f : Type u₀ → Type u₁) where
  map : ∀ {α β}, α ≃ β → f α → f β
  map_refl' : ∀ α, map (Equivₓ.refl α) = @id (f α) := by
    run_tac
      obviously
  map_trans' : ∀ {α β γ} (k : α ≃ β) (h : β ≃ γ), map (k.trans h) = map h ∘ map k := by
    run_tac
      obviously

restate_axiom EquivFunctor.map_refl'

restate_axiom EquivFunctor.map_trans'

attribute [simp] EquivFunctor.map_refl

namespace EquivFunctor

section

variable (f : Type u₀ → Type u₁) [EquivFunctor f] {α β : Type u₀} (e : α ≃ β)

/-- An `equiv_functor` in fact takes every equiv to an equiv. -/
def mapEquiv : f α ≃ f β where
  toFun := EquivFunctor.map e
  invFun := EquivFunctor.map e.symm
  left_inv := fun x => by
    convert (congr_fun (EquivFunctor.map_trans e e.symm) x).symm
    simp
  right_inv := fun y => by
    convert (congr_fun (EquivFunctor.map_trans e.symm e) y).symm
    simp

@[simp]
theorem map_equiv_apply (x : f α) : mapEquiv f e x = EquivFunctor.map e x :=
  rfl

theorem map_equiv_symm_apply (y : f β) : (mapEquiv f e).symm y = EquivFunctor.map e.symm y :=
  rfl

@[simp]
theorem map_equiv_refl (α) : mapEquiv f (Equivₓ.refl α) = Equivₓ.refl (f α) := by
  simpa [← EquivFunctor.mapEquiv]

@[simp]
theorem map_equiv_symm : (mapEquiv f e).symm = mapEquiv f e.symm :=
  Equivₓ.ext <| map_equiv_symm_apply f e

/-- The composition of `map_equiv`s is carried over the `equiv_functor`.
For plain `functor`s, this lemma is named `map_map` when applied
or `map_comp_map` when not applied.
-/
@[simp]
theorem map_equiv_trans {γ : Type u₀} (ab : α ≃ β) (bc : β ≃ γ) :
    (mapEquiv f ab).trans (mapEquiv f bc) = mapEquiv f (ab.trans bc) :=
  Equivₓ.ext fun x => by
    simp [← map_equiv, ← map_trans']

end

instance (priority := 100) ofIsLawfulFunctor (f : Type u₀ → Type u₁) [Functor f] [IsLawfulFunctor f] :
    EquivFunctor f where
  map := fun α β e => Functor.map e
  map_refl' := fun α => by
    ext
    apply IsLawfulFunctor.id_map
  map_trans' := fun α β γ k h => by
    ext x
    apply IsLawfulFunctor.comp_map k h x

theorem mapEquiv.injective (f : Type u₀ → Type u₁) [Applicativeₓ f] [IsLawfulApplicative f] {α β : Type u₀}
    (h : ∀ γ, Function.Injective (pure : γ → f γ)) : Function.Injective (@EquivFunctor.mapEquiv f _ α β) :=
  fun e₁ e₂ H =>
  Equivₓ.ext fun x =>
    h β
      (by
        simpa [← EquivFunctor.map] using Equivₓ.congr_fun H (pure x))

end EquivFunctor

