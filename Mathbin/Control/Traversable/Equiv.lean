/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Control.Traversable.Lemmas
import Mathbin.Logic.Equiv.Basic

/-!
# Transferring `traversable` instances along isomorphisms

This file allows to transfer `traversable` instances along isomorphisms.

## Main declarations

* `equiv.map`: Turns functorially a function `α → β` into a function `t' α → t' β` using the functor
  `t` and the equivalence `Π α, t α ≃ t' α`.
* `equiv.functor`: `equiv.map` as a functor.
* `equiv.traverse`: Turns traversably a function `α → m β` into a function `t' α → m (t' β)` using
  the traversable functor `t` and the equivalence `Π α, t α ≃ t' α`.
* `equiv.traversable`: `equiv.traverse` as a traversable functor.
* `equiv.is_lawful_traversable`: `equiv.traverse` as a lawful traversable functor.
-/


universe u

namespace Equivₓ

section Functor

parameter {t t' : Type u → Type u}

parameter (eqv : ∀ α, t α ≃ t' α)

variable [Functor t]

open Functor

/-- Given a functor `t`, a function `t' : Type u → Type u`, and
equivalences `t α ≃ t' α` for all `α`, then every function `α → β` can
be mapped to a function `t' α → t' β` functorially (see
`equiv.functor`). -/
protected def map {α β : Type u} (f : α → β) (x : t' α) : t' β :=
  eqv β <| map f ((eqv α).symm x)

/-- The function `equiv.map` transfers the functoriality of `t` to
`t'` using the equivalences `eqv`.  -/
protected def functor : Functor t' where map := @Equivₓ.map _

variable [IsLawfulFunctor t]

protected theorem id_map {α : Type u} (x : t' α) : Equivₓ.map id x = x := by
  simp [← Equivₓ.map, ← id_map]

protected theorem comp_map {α β γ : Type u} (g : α → β) (h : β → γ) (x : t' α) :
    Equivₓ.map (h ∘ g) x = Equivₓ.map h (Equivₓ.map g x) := by
  simp [← Equivₓ.map] <;> apply comp_map

protected theorem is_lawful_functor : @IsLawfulFunctor _ Equivₓ.functor :=
  { id_map := @Equivₓ.id_map _ _, comp_map := @Equivₓ.comp_map _ _ }

protected theorem is_lawful_functor' [F : Functor t'] (h₀ : ∀ {α β} (f : α → β), Functor.map f = Equivₓ.map f)
    (h₁ : ∀ {α β} (f : β), Functor.mapConst f = (Equivₓ.map ∘ Function.const α) f) : IsLawfulFunctor t' := by
  have : F = Equivₓ.functor := by
    cases F
    dsimp' [← Equivₓ.functor]
    congr <;> ext <;> [rw [← h₀], rw [← h₁]]
  subst this
  exact Equivₓ.is_lawful_functor

end Functor

section Traversable

parameter {t t' : Type u → Type u}

parameter (eqv : ∀ α, t α ≃ t' α)

variable [Traversable t]

variable {m : Type u → Type u} [Applicativeₓ m]

variable {α β : Type u}

/-- Like `equiv.map`, a function `t' : Type u → Type u` can be given
the structure of a traversable functor using a traversable functor
`t'` and equivalences `t α ≃ t' α` for all α.  See `equiv.traversable`. -/
protected def traverse (f : α → m β) (x : t' α) : m (t' β) :=
  eqv β <$> traverse f ((eqv α).symm x)

/-- The function `equiv.traverse` transfers a traversable functor
instance across the equivalences `eqv`. -/
protected def traversable : Traversable t' where
  toFunctor := Equivₓ.functor eqv
  traverse := @Equivₓ.traverse _

end Traversable

section Equivₓ

parameter {t t' : Type u → Type u}

parameter (eqv : ∀ α, t α ≃ t' α)

variable [Traversable t] [IsLawfulTraversable t]

variable {F G : Type u → Type u} [Applicativeₓ F] [Applicativeₓ G]

variable [IsLawfulApplicative F] [IsLawfulApplicative G]

variable (η : ApplicativeTransformation F G)

variable {α β γ : Type u}

open IsLawfulTraversable Functor

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
protected theorem id_traverse (x : t' α) : Equivₓ.traverse eqv id.mk x = x := by
  simp' [← Equivₓ.traverse, ← idBind, ← id_traverse, ← Functor.map] with functor_norm

protected theorem traverse_eq_map_id (f : α → β) (x : t' α) :
    Equivₓ.traverse eqv (id.mk ∘ f) x = id.mk (Equivₓ.map eqv f x) := by
  simp' [← Equivₓ.traverse, ← traverse_eq_map_id] with functor_norm <;> rfl

protected theorem comp_traverse (f : β → F γ) (g : α → G β) (x : t' α) :
    Equivₓ.traverse eqv (comp.mk ∘ Functor.map f ∘ g) x = Comp.mk (Equivₓ.traverse eqv f <$> Equivₓ.traverse eqv g x) :=
  by
  simp' [← Equivₓ.traverse, ← comp_traverse] with functor_norm <;> congr <;> ext <;> simp

protected theorem naturality (f : α → F β) (x : t' α) :
    η (Equivₓ.traverse eqv f x) = Equivₓ.traverse eqv (@η _ ∘ f) x := by
  simp' only [← Equivₓ.traverse] with functor_norm

/-- The fact that `t` is a lawful traversable functor carries over the
equivalences to `t'`, with the traversable functor structure given by
`equiv.traversable`. -/
protected def isLawfulTraversable : @IsLawfulTraversable t' (Equivₓ.traversable eqv) where
  to_is_lawful_functor := @Equivₓ.is_lawful_functor _ _ eqv _ _
  id_traverse := @Equivₓ.id_traverse _ _
  comp_traverse := @Equivₓ.comp_traverse _ _
  traverse_eq_map_id := @Equivₓ.traverse_eq_map_id _ _
  naturality := @Equivₓ.naturality _ _

/-- If the `traversable t'` instance has the properties that `map`,
`map_const`, and `traverse` are equal to the ones that come from
carrying the traversable functor structure from `t` over the
equivalences, then the fact that `t` is a lawful traversable functor
carries over as well. -/
protected def isLawfulTraversable' [_i : Traversable t'] (h₀ : ∀ {α β} (f : α → β), map f = Equivₓ.map eqv f)
    (h₁ : ∀ {α β} (f : β), mapConst f = (Equivₓ.map eqv ∘ Function.const α) f)
    (h₂ :
      ∀ {F : Type u → Type u} [Applicativeₓ F],
        ∀ [IsLawfulApplicative F] {α β} (f : α → F β), traverse f = Equivₓ.traverse eqv f) :
    IsLawfulTraversable t' := by
  -- we can't use the same approach as for `is_lawful_functor'` because
    -- h₂ needs a `is_lawful_applicative` assumption
    refine' { to_is_lawful_functor := Equivₓ.is_lawful_functor' eqv @h₀ @h₁.. } <;>
    intros
  · rw [h₂, Equivₓ.id_traverse]
    infer_instance
    
  · rw [h₂, Equivₓ.comp_traverse f g x, h₂]
    congr
    rw [h₂]
    all_goals
      infer_instance
    
  · rw [h₂, Equivₓ.traverse_eq_map_id, h₀] <;> infer_instance
    
  · rw [h₂, Equivₓ.naturality, h₂] <;> infer_instance
    

end Equivₓ

end Equivₓ

