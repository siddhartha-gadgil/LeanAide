/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Scott Morrison
-/
import Mathbin.Data.Finset.Lattice
import Mathbin.Data.Multiset.Functor

/-!
# Functoriality of `finset`

This file defines the functor structure of `finset`.

## TODO

Currently, all instances are classical because the functor classes want to run over all types. If
instead we could state that a functor is lawful/applicative/traversable... between two given types,
then we could provide the instances for types with decidable equality.
-/


universe u

open Function

namespace Finset

/-! ### Functor -/


section Functor

variable {α β : Type u} [∀ P, Decidable P]

/-- Because `finset.image` requires a `decidable_eq` instance for the target type, we can only
construct `functor finset` when working classically. -/
instance : Functor Finset where map := fun α β f s => s.Image f

instance : IsLawfulFunctor Finset where
  id_map := fun α s => image_id
  comp_map := fun α β γ f g s => image_image.symm

@[simp]
theorem fmap_def {s : Finset α} (f : α → β) : f <$> s = s.Image f :=
  rfl

end Functor

/-! ### Pure -/


instance : Pure Finset :=
  ⟨fun α x => {x}⟩

@[simp]
theorem pure_def {α} : (pure : α → Finset α) = singleton :=
  rfl

/-! ### Applicative functor -/


section Applicativeₓ

variable {α β : Type u} [∀ P, Decidable P]

instance : Applicativeₓ Finset :=
  { Finset.functor, Finset.hasPure with seq := fun α β t s => t.sup fun f => s.Image f,
    seqLeft := fun α β s t => if t = ∅ then ∅ else s, seqRight := fun α β s t => if s = ∅ then ∅ else t }

@[simp]
theorem seq_def (s : Finset α) (t : Finset (α → β)) : t <*> s = t.sup fun f => s.Image f :=
  rfl

@[simp]
theorem seq_left_def (s : Finset α) (t : Finset β) : s <* t = if t = ∅ then ∅ else s :=
  rfl

@[simp]
theorem seq_right_def (s : Finset α) (t : Finset β) : s *> t = if s = ∅ then ∅ else t :=
  rfl

instance : IsLawfulApplicative Finset :=
  { Finset.is_lawful_functor with
    seq_left_eq := fun α β s t => by
      rw [seq_def, fmap_def, seq_left_def]
      obtain rfl | ht := t.eq_empty_or_nonempty
      · simp_rw [if_pos rfl, image_empty]
        exact (sup_bot _).symm
        
      · ext a
        rw [if_neg ht.ne_empty, mem_sup]
        refine' ⟨fun ha => ⟨const β a, mem_image_of_mem _ ha, mem_image_const_self.2 ht⟩, _⟩
        rintro ⟨f, hf, ha⟩
        rw [mem_image] at hf ha
        obtain ⟨b, hb, rfl⟩ := hf
        obtain ⟨_, _, rfl⟩ := ha
        exact hb
        ,
    seq_right_eq := fun α β s t => by
      rw [seq_def, fmap_def, seq_right_def]
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [if_pos rfl, image_empty, sup_empty, bot_eq_empty]
        
      · ext a
        rw [if_neg hs.ne_empty, mem_sup]
        refine'
          ⟨fun ha =>
            ⟨id, mem_image_const_self.2 hs, by
              rwa [image_id]⟩,
            _⟩
        rintro ⟨f, hf, ha⟩
        rw [mem_image] at hf ha
        obtain ⟨b, hb, rfl⟩ := ha
        obtain ⟨_, _, rfl⟩ := hf
        exact hb
        ,
    pure_seq_eq_map := fun α β f s => sup_singleton, map_pure := fun α β f a => image_singleton _ _,
    seq_pure := fun α β s a => sup_singleton'' _ _,
    seq_assoc := fun α β γ s t u => by
      ext a
      simp_rw [seq_def, fmap_def]
      simp only [← exists_prop, ← mem_sup, ← mem_image]
      constructor
      · rintro ⟨g, hg, b, ⟨f, hf, a, ha, rfl⟩, rfl⟩
        exact ⟨g ∘ f, ⟨comp g, ⟨g, hg, rfl⟩, f, hf, rfl⟩, a, ha, rfl⟩
        
      · rintro ⟨c, ⟨_, ⟨g, hg, rfl⟩, f, hf, rfl⟩, a, ha, rfl⟩
        exact ⟨g, hg, f a, ⟨f, hf, a, ha, rfl⟩, rfl⟩
         }

instance : IsCommApplicative Finset :=
  { Finset.is_lawful_applicative with
    commutative_prod := fun α β s t => by
      simp_rw [seq_def, fmap_def, sup_image, sup_eq_bUnion]
      change (s.bUnion fun a => t.image fun b => (a, b)) = t.bUnion fun b => s.image fun a => (a, b)
      trans s.product t <;> [rw [product_eq_bUnion], rw [product_eq_bUnion_right]] <;>
        congr <;> ext <;> simp_rw [mem_image] }

end Applicativeₓ

/-! ### Monad -/


section Monadₓ

variable [∀ P, Decidable P]

instance : Monadₓ Finset :=
  { Finset.applicative with bind := fun α β => @sup _ _ _ _ }

@[simp]
theorem bind_def {α β} : (· >>= ·) = @sup (Finset α) β _ _ :=
  rfl

instance : IsLawfulMonad Finset :=
  { Finset.is_lawful_applicative with bind_pure_comp_eq_map := fun α β f s => sup_singleton'' _ _,
    bind_map_eq_seq := fun α β t s => rfl, pure_bind := fun α β t s => sup_singleton,
    bind_assoc := fun α β γ s f g => by
      convert sup_bUnion _ _
      exact sup_eq_bUnion _ _ }

end Monadₓ

/-! ### Alternative functor -/


section Alternativeₓ

variable [∀ P, Decidable P]

instance : Alternativeₓ Finset :=
  { Finset.applicative with orelse := fun α => (· ∪ ·), failure := fun α => ∅ }

end Alternativeₓ

/-! ### Traversable functor -/


section Traversable

variable {α β γ : Type u} {F G : Type u → Type u} [Applicativeₓ F] [Applicativeₓ G] [IsCommApplicative F]
  [IsCommApplicative G]

/-- Traverse function for `finset`. -/
def traverse [DecidableEq β] (f : α → F β) (s : Finset α) : F (Finset β) :=
  Multiset.toFinset <$> Multiset.traverse f s.1

@[simp]
theorem id_traverse [DecidableEq α] (s : Finset α) : traverse id.mk s = s := by
  rw [traverse, Multiset.id_traverse]
  exact s.val_to_finset

open Classical

@[simp]
theorem map_comp_coe (h : α → β) : Functor.map h ∘ Multiset.toFinset = Multiset.toFinset ∘ Functor.map h :=
  funext fun s => image_to_finset

theorem map_traverse (g : α → G β) (h : β → γ) (s : Finset α) :
    Functor.map h <$> traverse g s = traverse (Functor.map h ∘ g) s := by
  unfold traverse
  simp' only [← map_comp_coe] with functor_norm
  rw [IsLawfulFunctor.comp_map, Multiset.map_traverse]

end Traversable

end Finset

