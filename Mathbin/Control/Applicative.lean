/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Control.Functor

/-!
# `applicative` instances

This file provides `applicative` instances for concrete functors:
* `id`
* `functor.comp`
* `functor.const`
* `functor.add_const`
-/


universe u v w

section Lemmas

open Function

variable {F : Type u → Type v}

variable [Applicativeₓ F] [IsLawfulApplicative F]

variable {α β γ σ : Type u}

theorem Applicativeₓ.map_seq_map (f : α → β → γ) (g : σ → β) (x : F α) (y : F σ) :
    f <$> x <*> g <$> y = (flip (· ∘ ·) g ∘ f) <$> x <*> y := by
  simp' [← flip] with functor_norm

theorem Applicativeₓ.pure_seq_eq_map' (f : α → β) : (· <*> ·) (pure f : F (α → β)) = (· <$> ·) f := by
  ext <;> simp' with functor_norm

theorem Applicativeₓ.ext {F} :
    ∀ {A1 : Applicativeₓ F} {A2 : Applicativeₓ F} [@IsLawfulApplicative F A1] [@IsLawfulApplicative F A2]
      (H1 : ∀ {α : Type u} (x : α), @Pure.pure _ A1.toHasPure _ x = @Pure.pure _ A2.toHasPure _ x)
      (H2 :
        ∀ {α β : Type u} (f : F (α → β)) (x : F α), @Seqₓ.seq _ A1.toHasSeq _ _ f x = @Seqₓ.seq _ A2.toHasSeq _ _ f x),
      A1 = A2
  | { toFunctor := F1, seq := s1, pure := p1, seqLeft := sl1, seqRight := sr1 },
    { toFunctor := F2, seq := s2, pure := p2, seqLeft := sl2, seqRight := sr2 }, L1, L2, H1, H2 => by
    obtain rfl : @p1 = @p2 := by
      funext α x
      apply H1
    obtain rfl : @s1 = @s2 := by
      funext α β f x
      apply H2
    cases L1
    cases L2
    obtain rfl : F1 = F2 := by
      skip
      apply Functor.ext
      intros
      exact (L1_pure_seq_eq_map _ _).symm.trans (L2_pure_seq_eq_map _ _)
    congr <;> funext α β x y
    · exact (L1_seq_left_eq _ _).trans (L2_seq_left_eq _ _).symm
      
    · exact (L1_seq_right_eq _ _).trans (L2_seq_right_eq _ _).symm
      

end Lemmas

instance : IsCommApplicative id := by
  refine' { .. } <;> intros <;> rfl

namespace Functor

namespace Comp

open Function hiding comp

open Functor

variable {F : Type u → Type w} {G : Type v → Type u}

variable [Applicativeₓ F] [Applicativeₓ G]

variable [IsLawfulApplicative F] [IsLawfulApplicative G]

variable {α β γ : Type v}

theorem map_pure (f : α → β) (x : α) : (f <$> pure x : Comp F G β) = pure (f x) :=
  comp.ext <| by
    simp

theorem seq_pure (f : Comp F G (α → β)) (x : α) : f <*> pure x = (fun g : α → β => g x) <$> f :=
  comp.ext <| by
    simp' [← (· ∘ ·)] with functor_norm

theorem seq_assoc (x : Comp F G α) (f : Comp F G (α → β)) (g : Comp F G (β → γ)) :
    g <*> (f <*> x) = @Function.comp α β γ <$> g <*> f <*> x :=
  comp.ext <| by
    simp' [← (· ∘ ·)] with functor_norm

theorem pure_seq_eq_map (f : α → β) (x : Comp F G α) : pure f <*> x = f <$> x :=
  comp.ext <| by
    simp' [← Applicativeₓ.pure_seq_eq_map'] with functor_norm

instance : IsLawfulApplicative (Comp F G) where
  pure_seq_eq_map := @Comp.pure_seq_eq_map F G _ _ _ _
  map_pure := @Comp.map_pure F G _ _ _ _
  seq_pure := @Comp.seq_pure F G _ _ _ _
  seq_assoc := @Comp.seq_assoc F G _ _ _ _

theorem applicative_id_comp {F} [AF : Applicativeₓ F] [LF : IsLawfulApplicative F] : @Comp.applicative id F _ _ = AF :=
  @Applicativeₓ.ext F _ _ (@Comp.is_lawful_applicative id F _ _ _ _) _ (fun α x => rfl) fun α β f x => rfl

theorem applicative_comp_id {F} [AF : Applicativeₓ F] [LF : IsLawfulApplicative F] : @Comp.applicative F id _ _ = AF :=
  @Applicativeₓ.ext F _ _ (@Comp.is_lawful_applicative F id _ _ _ _) _ (fun α x => rfl) fun α β f x =>
    show id <$> f <*> x = f <*> x by
      rw [id_map]

open IsCommApplicative

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
instance {f : Type u → Type w} {g : Type v → Type u} [Applicativeₓ f] [Applicativeₓ g] [IsCommApplicative f]
    [IsCommApplicative g] : IsCommApplicative (Comp f g) := by
  refine' { @comp.is_lawful_applicative f g _ _ _ _ with .. }
  intros
  casesm* comp _ _ _
  simp' [← map, ← Seqₓ.seq] with functor_norm
  rw [commutative_map]
  simp' [← comp.mk, ← flip, ← (· ∘ ·)] with functor_norm
  congr
  funext
  rw [commutative_map]
  congr

end Comp

end Functor

open Functor

@[functor_norm]
theorem Comp.seq_mk {α β : Type w} {f : Type u → Type v} {g : Type w → Type u} [Applicativeₓ f] [Applicativeₓ g]
    (h : f (g (α → β))) (x : f (g α)) : Comp.mk h <*> Comp.mk x = Comp.mk (Seqₓ.seq <$> h <*> x) :=
  rfl

instance {α} [One α] [Mul α] : Applicativeₓ (Const α) where
  pure := fun β x => (1 : α)
  seq := fun β γ f x => (f * x : α)

instance {α} [Monoidₓ α] : IsLawfulApplicative (Const α) := by
  refine' { .. } <;> intros <;> simp [← mul_assoc, ← (· <$> ·), ← (· <*> ·), ← pure]

instance {α} [Zero α] [Add α] : Applicativeₓ (AddConst α) where
  pure := fun β x => (0 : α)
  seq := fun β γ f x => (f + x : α)

instance {α} [AddMonoidₓ α] : IsLawfulApplicative (AddConst α) := by
  refine' { .. } <;> intros <;> simp [← add_assocₓ, ← (· <$> ·), ← (· <*> ·), ← pure]

