/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Simon Hudon, Kenny Lau
-/
import Mathbin.Data.Multiset.Bind
import Mathbin.Control.Traversable.Lemmas
import Mathbin.Control.Traversable.Instances

/-!
# Functoriality of `multiset`.
-/


universe u

namespace Multiset

open List

instance : Functor Multiset where map := @map

@[simp]
theorem fmap_def {α' β'} {s : Multiset α'} (f : α' → β') : f <$> s = s.map f :=
  rfl

instance : IsLawfulFunctor Multiset := by
  refine' { .. } <;> intros <;> simp

open IsLawfulTraversable IsCommApplicative

variable {F : Type u → Type u} [Applicativeₓ F] [IsCommApplicative F]

variable {α' β' : Type u} (f : α' → F β')

def traverse : Multiset α' → F (Multiset β') :=
  Quotientₓ.lift (Functor.map coe ∘ Traversable.traverse f)
    (by
      introv p
      unfold Function.comp
      induction p
      case perm.nil =>
        rfl
      case perm.cons =>
        have :
          Multiset.cons <$> f p_x <*> coe <$> traverse f p_l₁ = Multiset.cons <$> f p_x <*> coe <$> traverse f p_l₂ :=
          by
          rw [p_ih]
        simpa with functor_norm
      case perm.swap =>
        have :
          (fun a b (l : List β') => (↑(a :: b :: l) : Multiset β')) <$> f p_y <*> f p_x =
            (fun a b l => ↑(a :: b :: l)) <$> f p_x <*> f p_y :=
          by
          rw [IsCommApplicative.commutative_map]
          congr
          funext a b l
          simpa [← flip] using perm.swap b a l
        simp' [← (· ∘ ·), ← this] with functor_norm
      case perm.trans =>
        simp [*])

instance : Monadₓ Multiset :=
  { Multiset.functor with pure := fun α x => {x}, bind := @bind }

@[simp]
theorem pure_def {α} : (pure : α → Multiset α) = singleton :=
  rfl

@[simp]
theorem bind_def {α β} : (· >>= ·) = @bind α β :=
  rfl

instance : IsLawfulMonad Multiset where
  bind_pure_comp_eq_map := fun α β f s =>
    (Multiset.induction_on s rfl) fun a s ih => by
      simp
  pure_bind := fun α β x f => by
    simp [← pure]
  bind_assoc := @bind_assoc

open Functor

open Traversable IsLawfulTraversable

@[simp]
theorem lift_coe {α β : Type _} (x : List α) (f : List α → β) (h : ∀ a b : List α, a ≈ b → f a = f b) :
    Quotientₓ.lift f h (x : Multiset α) = f x :=
  Quotientₓ.lift_mk _ _ _

@[simp]
theorem map_comp_coe {α β} (h : α → β) : Functor.map h ∘ coe = (coe ∘ Functor.map h : List α → Multiset β) := by
  funext <;> simp [← Functor.map]

theorem id_traverse {α : Type _} (x : Multiset α) : traverse id.mk x = x :=
  Quotientₓ.induction_on x
    (by
      intro
      simp [← traverse]
      rfl)

theorem comp_traverse {G H : Type _ → Type _} [Applicativeₓ G] [Applicativeₓ H] [IsCommApplicative G]
    [IsCommApplicative H] {α β γ : Type _} (g : α → G β) (h : β → H γ) (x : Multiset α) :
    traverse (comp.mk ∘ Functor.map h ∘ g) x = Comp.mk (Functor.map (traverse h) (traverse g x)) :=
  Quotientₓ.induction_on x
    (by
      intro <;>
        simp' [← traverse, ← comp_traverse] with functor_norm <;> simp' [← (· <$> ·), ← (· ∘ ·)] with functor_norm)

theorem map_traverse {G : Type _ → Type _} [Applicativeₓ G] [IsCommApplicative G] {α β γ : Type _} (g : α → G β)
    (h : β → γ) (x : Multiset α) : Functor.map (Functor.map h) (traverse g x) = traverse (Functor.map h ∘ g) x :=
  Quotientₓ.induction_on x
    (by
      intro <;> simp' [← traverse] with functor_norm <;> rw [IsLawfulFunctor.comp_map, map_traverse])

theorem traverse_map {G : Type _ → Type _} [Applicativeₓ G] [IsCommApplicative G] {α β γ : Type _} (g : α → β)
    (h : β → G γ) (x : Multiset α) : traverse h (map g x) = traverse (h ∘ g) x :=
  Quotientₓ.induction_on x
    (by
      intro <;> simp [← traverse] <;> rw [← Traversable.traverse_map h g] <;> [rfl, infer_instance])

theorem naturality {G H : Type _ → Type _} [Applicativeₓ G] [Applicativeₓ H] [IsCommApplicative G] [IsCommApplicative H]
    (eta : ApplicativeTransformation G H) {α β : Type _} (f : α → G β) (x : Multiset α) :
    eta (traverse f x) = traverse (@eta _ ∘ f) x :=
  Quotientₓ.induction_on x
    (by
      intro <;> simp' [← traverse, ← IsLawfulTraversable.naturality] with functor_norm)

end Multiset

