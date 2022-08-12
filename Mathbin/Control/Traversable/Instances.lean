/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Control.Applicative
import Mathbin.Data.List.Forall2
import Mathbin.Data.Set.Functor

/-!
# Traversable instances

This file provides instances of `traversable` for types from the core library: `option`, `list` and
`sum`.
-/


universe u v

section Option

open Functor

variable {F G : Type u → Type u}

variable [Applicativeₓ F] [Applicativeₓ G]

variable [IsLawfulApplicative F] [IsLawfulApplicative G]

theorem Option.id_traverse {α} (x : Option α) : Option.traverseₓₓ id.mk x = x := by
  cases x <;> rfl

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
@[nolint unused_arguments]
theorem Option.comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : Option α) :
    Option.traverseₓₓ (comp.mk ∘ (· <$> ·) f ∘ g) x = Comp.mk (Option.traverseₓₓ f <$> Option.traverseₓₓ g x) := by
  cases x <;> simp' with functor_norm <;> rfl

theorem Option.traverse_eq_map_id {α β} (f : α → β) (x : Option α) : traverse (id.mk ∘ f) x = id.mk (f <$> x) := by
  cases x <;> rfl

variable (η : ApplicativeTransformation F G)

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
theorem Option.naturality {α β} (f : α → F β) (x : Option α) :
    η (Option.traverseₓₓ f x) = Option.traverseₓₓ (@η _ ∘ f) x := by
  cases' x with x <;> simp' [*] with functor_norm

end Option

instance : IsLawfulTraversable Option :=
  { Option.is_lawful_monad with id_traverse := @Option.id_traverse, comp_traverse := @Option.comp_traverse,
    traverse_eq_map_id := @Option.traverse_eq_map_id, naturality := @Option.naturality }

namespace List

variable {F G : Type u → Type u}

variable [Applicativeₓ F] [Applicativeₓ G]

section

variable [IsLawfulApplicative F] [IsLawfulApplicative G]

open Applicativeₓ Functor List

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
protected theorem id_traverse {α} (xs : List α) : List.traverseₓₓ id.mk xs = xs := by
  induction xs <;> simp' [*] with functor_norm <;> rfl

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
@[nolint unused_arguments]
protected theorem comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : List α) :
    List.traverseₓₓ (comp.mk ∘ (· <$> ·) f ∘ g) x = Comp.mk (List.traverseₓₓ f <$> List.traverseₓₓ g x) := by
  induction x <;> simp' [*] with functor_norm <;> rfl

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
protected theorem traverse_eq_map_id {α β} (f : α → β) (x : List α) : List.traverseₓₓ (id.mk ∘ f) x = id.mk (f <$> x) :=
  by
  induction x <;> simp' [*] with functor_norm <;> rfl

variable (η : ApplicativeTransformation F G)

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
protected theorem naturality {α β} (f : α → F β) (x : List α) :
    η (List.traverseₓₓ f x) = List.traverseₓₓ (@η _ ∘ f) x := by
  induction x <;> simp' [*] with functor_norm

open Nat

instance : IsLawfulTraversable.{u} List :=
  { List.is_lawful_monad with id_traverse := @List.id_traverse, comp_traverse := @List.comp_traverse,
    traverse_eq_map_id := @List.traverse_eq_map_id, naturality := @List.naturality }

end

section Traverse

variable {α' β' : Type u} (f : α' → F β')

@[simp]
theorem traverse_nil : traverse f ([] : List α') = (pure [] : F (List β')) :=
  rfl

@[simp]
theorem traverse_cons (a : α') (l : List α') : traverse f (a :: l) = (· :: ·) <$> f a <*> traverse f l :=
  rfl

variable [IsLawfulApplicative F]

@[simp]
theorem traverse_append : ∀ as bs : List α', traverse f (as ++ bs) = (· ++ ·) <$> traverse f as <*> traverse f bs
  | [], bs => by
    have : Append.append ([] : List β') = id := by
      funext <;> rfl
    simp' [← this] with functor_norm
  | a :: as, bs => by
    simp' [← traverse_append as bs] with functor_norm <;> congr

theorem mem_traverse {f : α' → Set β'} :
    ∀ (l : List α') (n : List β'), n ∈ traverse f l ↔ Forall₂ (fun b a => b ∈ f a) n l
  | [], [] => by
    simp
  | a :: as, [] => by
    simp
  | [], b :: bs => by
    simp
  | a :: as, b :: bs => by
    simp [← mem_traverse as bs]

end Traverse

end List

namespace Sum

section Traverse

variable {σ : Type u}

variable {F G : Type u → Type u}

variable [Applicativeₓ F] [Applicativeₓ G]

open Applicativeₓ Functor

open List (cons)

protected theorem traverse_map {α β γ : Type u} (g : α → β) (f : β → G γ) (x : Sum σ α) :
    Sum.traverseₓ f (g <$> x) = Sum.traverseₓ (f ∘ g) x := by
  cases x <;> simp' [← Sum.traverseₓ, ← id_map] with functor_norm <;> rfl

variable [IsLawfulApplicative F] [IsLawfulApplicative G]

protected theorem id_traverse {σ α} (x : Sum σ α) : Sum.traverseₓ id.mk x = x := by
  cases x <;> rfl

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
@[nolint unused_arguments]
protected theorem comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : Sum σ α) :
    Sum.traverseₓ (comp.mk ∘ (· <$> ·) f ∘ g) x = Comp.mk (Sum.traverseₓ f <$> Sum.traverseₓ g x) := by
  cases x <;> simp' [← Sum.traverseₓ, ← map_id] with functor_norm <;> rfl

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
protected theorem traverse_eq_map_id {α β} (f : α → β) (x : Sum σ α) : Sum.traverseₓ (id.mk ∘ f) x = id.mk (f <$> x) :=
  by
  induction x <;> simp' [*] with functor_norm <;> rfl

protected theorem map_traverse {α β γ} (g : α → G β) (f : β → γ) (x : Sum σ α) :
    (· <$> ·) f <$> Sum.traverseₓ g x = Sum.traverseₓ ((· <$> ·) f ∘ g) x := by
  cases x <;> simp' [← Sum.traverseₓ, ← id_map] with functor_norm <;> congr <;> rfl

variable (η : ApplicativeTransformation F G)

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
protected theorem naturality {α β} (f : α → F β) (x : Sum σ α) : η (Sum.traverseₓ f x) = Sum.traverseₓ (@η _ ∘ f) x :=
  by
  cases x <;> simp' [← Sum.traverseₓ] with functor_norm

end Traverse

instance {σ : Type u} : IsLawfulTraversable.{u} (Sum σ) :=
  { Sum.is_lawful_monad with id_traverse := @Sum.id_traverse σ, comp_traverse := @Sum.comp_traverse σ,
    traverse_eq_map_id := @Sum.traverse_eq_map_id σ, naturality := @Sum.naturality σ }

end Sum

