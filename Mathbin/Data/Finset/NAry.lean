/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Finset.Prod

/-!
# N-ary images of finsets

This file defines `finset.image₂`, the binary image of finsets. This is the finset version of
`set.image2`. This is mostly useful to define pointwise operations.

## Notes

This file is very similar to the n-ary section of `data.set.basic` and to `order.filter.n_ary`.
Please keep them in sync.

We do not define `finset.image₃` as its only purpose would be to prove properties of `finset.image₂`
and `set.image2` already fulfills this task.
-/


open Function Set

namespace Finset

variable {α α' β β' γ γ' δ δ' ε ε' : Type _} [DecidableEq α'] [DecidableEq β'] [DecidableEq γ] [DecidableEq γ']
  [DecidableEq δ] [DecidableEq δ'] [DecidableEq ε] [DecidableEq ε'] {f f' : α → β → γ} {g g' : α → β → γ → δ}
  {s s' : Finset α} {t t' : Finset β} {u u' : Finset γ} {a a' : α} {b b' : β} {c : γ}

/-- The image of a binary function `f : α → β → γ` as a function `finset α → finset β → finset γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def image₂ (f : α → β → γ) (s : Finset α) (t : Finset β) : Finset γ :=
  (s.product t).Image <| uncurry f

@[simp]
theorem mem_image₂ : c ∈ image₂ f s t ↔ ∃ a b, a ∈ s ∧ b ∈ t ∧ f a b = c := by
  simp [← image₂, ← and_assoc]

@[simp, norm_cast]
theorem coe_image₂ (f : α → β → γ) (s : Finset α) (t : Finset β) : (image₂ f s t : Set γ) = Set.Image2 f s t :=
  Set.ext fun _ => mem_image₂

theorem card_image₂_le (f : α → β → γ) (s : Finset α) (t : Finset β) : (image₂ f s t).card ≤ s.card * t.card :=
  card_image_le.trans_eq <| card_product _ _

theorem card_image₂_iff :
    (image₂ f s t).card = s.card * t.card ↔ ((s : Set α) ×ˢ (t : Set β) : Set (α × β)).InjOn fun x => f x.1 x.2 := by
  rw [← card_product, ← coe_product]
  exact card_image_iff

theorem card_image₂ (hf : Injective2 f) (s : Finset α) (t : Finset β) : (image₂ f s t).card = s.card * t.card :=
  (card_image_of_injective _ hf.uncurry).trans <| card_product _ _

theorem mem_image₂_of_mem (ha : a ∈ s) (hb : b ∈ t) : f a b ∈ image₂ f s t :=
  mem_image₂.2 ⟨a, b, ha, hb, rfl⟩

theorem mem_image₂_iff (hf : Injective2 f) : f a b ∈ image₂ f s t ↔ a ∈ s ∧ b ∈ t := by
  rw [← mem_coe, coe_image₂, mem_image2_iff hf, mem_coe, mem_coe]

theorem image₂_subset (hs : s ⊆ s') (ht : t ⊆ t') : image₂ f s t ⊆ image₂ f s' t' := by
  rw [← coe_subset, coe_image₂, coe_image₂]
  exact image2_subset hs ht

theorem image₂_subset_left (ht : t ⊆ t') : image₂ f s t ⊆ image₂ f s t' :=
  image₂_subset Subset.rfl ht

theorem image₂_subset_right (hs : s ⊆ s') : image₂ f s t ⊆ image₂ f s' t :=
  image₂_subset hs Subset.rfl

theorem image_subset_image₂_left (hb : b ∈ t) : (fun a => f a b) '' s ⊆ image₂ f s t :=
  ball_image_of_ball fun a ha => mem_image₂_of_mem ha hb

theorem image_subset_image₂_right (ha : a ∈ s) : f a '' t ⊆ image₂ f s t :=
  ball_image_of_ball fun b => mem_image₂_of_mem ha

theorem forall_image₂_iff {p : γ → Prop} : (∀, ∀ z ∈ image₂ f s t, ∀, p z) ↔ ∀, ∀ x ∈ s, ∀, ∀ y ∈ t, ∀, p (f x y) := by
  simp_rw [← mem_coe, coe_image₂, forall_image2_iff]

@[simp]
theorem image₂_subset_iff : image₂ f s t ⊆ u ↔ ∀, ∀ x ∈ s, ∀, ∀ y ∈ t, ∀, f x y ∈ u :=
  forall_image₂_iff

@[simp]
theorem image₂_nonempty_iff : (image₂ f s t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := by
  rw [← coe_nonempty, coe_image₂]
  exact image2_nonempty_iff

theorem Nonempty.image₂ (hs : s.Nonempty) (ht : t.Nonempty) : (image₂ f s t).Nonempty :=
  image₂_nonempty_iff.2 ⟨hs, ht⟩

theorem Nonempty.of_image₂_left (h : (image₂ f s t).Nonempty) : s.Nonempty :=
  (image₂_nonempty_iff.1 h).1

theorem Nonempty.of_image₂_right (h : (image₂ f s t).Nonempty) : t.Nonempty :=
  (image₂_nonempty_iff.1 h).2

@[simp]
theorem image₂_empty_left : image₂ f ∅ t = ∅ :=
  coe_injective <| by
    simp

@[simp]
theorem image₂_empty_right : image₂ f s ∅ = ∅ :=
  coe_injective <| by
    simp

@[simp]
theorem image₂_eq_empty_iff : image₂ f s t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  simp_rw [← not_nonempty_iff_eq_empty, image₂_nonempty_iff, not_and_distrib]

@[simp]
theorem image₂_singleton_left : image₂ f {a} t = t.Image fun b => f a b :=
  ext fun x => by
    simp

@[simp]
theorem image₂_singleton_right : image₂ f s {b} = s.Image fun a => f a b :=
  ext fun x => by
    simp

theorem image₂_singleton_left' : image₂ f {a} t = t.Image (f a) :=
  image₂_singleton_left

theorem image₂_singleton : image₂ f {a} {b} = {f a b} := by
  simp

theorem image₂_union_left [DecidableEq α] : image₂ f (s ∪ s') t = image₂ f s t ∪ image₂ f s' t :=
  coe_injective <| by
    push_cast
    exact image2_union_left

theorem image₂_union_right [DecidableEq β] : image₂ f s (t ∪ t') = image₂ f s t ∪ image₂ f s t' :=
  coe_injective <| by
    push_cast
    exact image2_union_right

theorem image₂_inter_subset_left [DecidableEq α] : image₂ f (s ∩ s') t ⊆ image₂ f s t ∩ image₂ f s' t :=
  coe_subset.1 <| by
    push_cast
    exact image2_inter_subset_left

theorem image₂_inter_subset_right [DecidableEq β] : image₂ f s (t ∩ t') ⊆ image₂ f s t ∩ image₂ f s t' :=
  coe_subset.1 <| by
    push_cast
    exact image2_inter_subset_right

theorem image₂_congr (h : ∀, ∀ a ∈ s, ∀, ∀ b ∈ t, ∀, f a b = f' a b) : image₂ f s t = image₂ f' s t :=
  coe_injective <| by
    push_cast
    exact image2_congr h

/-- A common special case of `image₂_congr` -/
theorem image₂_congr' (h : ∀ a b, f a b = f' a b) : image₂ f s t = image₂ f' s t :=
  image₂_congr fun a _ b _ => h a b

theorem subset_image₂ {s : Set α} {t : Set β} (hu : ↑u ⊆ Image2 f s t) :
    ∃ (s' : Finset α)(t' : Finset β), ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ image₂ f s' t' := by
  apply Finset.induction_on' u
  · exact ⟨∅, ∅, Set.empty_subset _, Set.empty_subset _, empty_subset _⟩
    
  rintro a u ha _ _ ⟨s', t', hs, hs', h⟩
  obtain ⟨x, y, hx, hy, ha⟩ := hu ha
  have := Classical.decEq α
  have := Classical.decEq β
  refine' ⟨insert x s', insert y t', _⟩
  simp_rw [coe_insert, Set.insert_subset]
  exact
    ⟨⟨hx, hs⟩, ⟨hy, hs'⟩,
      insert_subset.2
        ⟨mem_image₂.2 ⟨x, y, mem_insert_self _ _, mem_insert_self _ _, ha⟩,
          h.trans <| image₂_subset (subset_insert _ _) <| subset_insert _ _⟩⟩

theorem bUnion_image_left : (s.bUnion fun a => t.Image <| f a) = image₂ f s t :=
  coe_injective <| by
    push_cast
    exact Set.Union_image_left _

theorem bUnion_image_right : (t.bUnion fun b => s.Image fun a => f a b) = image₂ f s t :=
  coe_injective <| by
    push_cast
    exact Set.Union_image_right _

/-!
### Algebraic replacement rules

A collection of lemmas to transfer associativity, commutativity, distributivity, ... of operations
to the associativity, commutativity, distributivity, ... of `finset.image₂` of those operations.

The proof pattern is `image₂_lemma operation_lemma`. For example, `image₂_comm mul_comm` proves that
`image₂ (*) f g = image₂ (*) g f` in a `comm_semigroup`.
-/


theorem image_image₂ (f : α → β → γ) (g : γ → δ) : (image₂ f s t).Image g = image₂ (fun a b => g (f a b)) s t :=
  coe_injective <| by
    push_cast
    exact image_image2 _ _

theorem image₂_image_left (f : γ → β → δ) (g : α → γ) : image₂ f (s.Image g) t = image₂ (fun a b => f (g a) b) s t :=
  coe_injective <| by
    push_cast
    exact image2_image_left _ _

theorem image₂_image_right (f : α → γ → δ) (g : β → γ) : image₂ f s (t.Image g) = image₂ (fun a b => f a (g b)) s t :=
  coe_injective <| by
    push_cast
    exact image2_image_right _ _

theorem image₂_swap (f : α → β → γ) (s : Finset α) (t : Finset β) : image₂ f s t = image₂ (fun a b => f b a) t s :=
  coe_injective <| by
    push_cast
    exact image2_swap _ _ _

@[simp]
theorem image₂_left [DecidableEq α] (h : t.Nonempty) : image₂ (fun x y => x) s t = s :=
  coe_injective <| by
    push_cast
    exact image2_left h

@[simp]
theorem image₂_right [DecidableEq β] (h : s.Nonempty) : image₂ (fun x y => y) s t = t :=
  coe_injective <| by
    push_cast
    exact image2_right h

theorem image₂_assoc {γ : Type _} {u : Finset γ} {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε} {g' : β → γ → ε'}
    (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) : image₂ f (image₂ g s t) u = image₂ f' s (image₂ g' t u) :=
  coe_injective <| by
    push_cast
    exact image2_assoc h_assoc

theorem image₂_comm {g : β → α → γ} (h_comm : ∀ a b, f a b = g b a) : image₂ f s t = image₂ g t s :=
  (image₂_swap _ _ _).trans <| by
    simp_rw [h_comm]

theorem image₂_left_comm {γ : Type _} {u : Finset γ} {f : α → δ → ε} {g : β → γ → δ} {f' : α → γ → δ'} {g' : β → δ' → ε}
    (h_left_comm : ∀ a b c, f a (g b c) = g' b (f' a c)) : image₂ f s (image₂ g t u) = image₂ g' t (image₂ f' s u) :=
  coe_injective <| by
    push_cast
    exact image2_left_comm h_left_comm

theorem image₂_right_comm {γ : Type _} {u : Finset γ} {f : δ → γ → ε} {g : α → β → δ} {f' : α → γ → δ'}
    {g' : δ' → β → ε} (h_right_comm : ∀ a b c, f (g a b) c = g' (f' a c) b) :
    image₂ f (image₂ g s t) u = image₂ g' (image₂ f' s u) t :=
  coe_injective <| by
    push_cast
    exact image2_right_comm h_right_comm

theorem image_image₂_distrib {g : γ → δ} {f' : α' → β' → δ} {g₁ : α → α'} {g₂ : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' (g₁ a) (g₂ b)) : (image₂ f s t).Image g = image₂ f' (s.Image g₁) (t.Image g₂) :=
  coe_injective <| by
    push_cast
    exact image_image2_distrib h_distrib

/-- Symmetric of `finset.image₂_image_left_comm`. -/
theorem image_image₂_distrib_left {g : γ → δ} {f' : α' → β → δ} {g' : α → α'}
    (h_distrib : ∀ a b, g (f a b) = f' (g' a) b) : (image₂ f s t).Image g = image₂ f' (s.Image g') t :=
  coe_injective <| by
    push_cast
    exact image_image2_distrib_left h_distrib

/-- Symmetric of `finset.image_image₂_right_comm`. -/
theorem image_image₂_distrib_right {g : γ → δ} {f' : α → β' → δ} {g' : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' a (g' b)) : (image₂ f s t).Image g = image₂ f' s (t.Image g') :=
  coe_injective <| by
    push_cast
    exact image_image2_distrib_right h_distrib

/-- Symmetric of `finset.image_image₂_distrib_left`. -/
theorem image₂_image_left_comm {f : α' → β → γ} {g : α → α'} {f' : α → β → δ} {g' : δ → γ}
    (h_left_comm : ∀ a b, f (g a) b = g' (f' a b)) : image₂ f (s.Image g) t = (image₂ f' s t).Image g' :=
  (image_image₂_distrib_left fun a b => (h_left_comm a b).symm).symm

/-- Symmetric of `finset.image_image₂_distrib_right`. -/
theorem image_image₂_right_comm {f : α → β' → γ} {g : β → β'} {f' : α → β → δ} {g' : δ → γ}
    (h_right_comm : ∀ a b, f a (g b) = g' (f' a b)) : image₂ f s (t.Image g) = (image₂ f' s t).Image g' :=
  (image_image₂_distrib_right fun a b => (h_right_comm a b).symm).symm

/-- The other direction does not hold because of the `s`-`s` cross terms on the RHS. -/
theorem image₂_distrib_subset_left {γ : Type _} {u : Finset γ} {f : α → δ → ε} {g : β → γ → δ} {f₁ : α → β → β'}
    {f₂ : α → γ → γ'} {g' : β' → γ' → ε} (h_distrib : ∀ a b c, f a (g b c) = g' (f₁ a b) (f₂ a c)) :
    image₂ f s (image₂ g t u) ⊆ image₂ g' (image₂ f₁ s t) (image₂ f₂ s u) :=
  coe_subset.1 <| by
    push_cast
    exact Set.image2_distrib_subset_left h_distrib

/-- The other direction does not hold because of the `u`-`u` cross terms on the RHS. -/
theorem image₂_distrib_subset_right {γ : Type _} {u : Finset γ} {f : δ → γ → ε} {g : α → β → δ} {f₁ : α → γ → α'}
    {f₂ : β → γ → β'} {g' : α' → β' → ε} (h_distrib : ∀ a b c, f (g a b) c = g' (f₁ a c) (f₂ b c)) :
    image₂ f (image₂ g s t) u ⊆ image₂ g' (image₂ f₁ s u) (image₂ f₂ t u) :=
  coe_subset.1 <| by
    push_cast
    exact Set.image2_distrib_subset_right h_distrib

theorem image_image₂_antidistrib {g : γ → δ} {f' : β' → α' → δ} {g₁ : β → β'} {g₂ : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g₁ b) (g₂ a)) :
    (image₂ f s t).Image g = image₂ f' (t.Image g₁) (s.Image g₂) := by
  rw [image₂_swap f]
  exact image_image₂_distrib fun _ _ => h_antidistrib _ _

/-- Symmetric of `finset.image₂_image_left_anticomm`. -/
theorem image_image₂_antidistrib_left {g : γ → δ} {f' : β' → α → δ} {g' : β → β'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g' b) a) : (image₂ f s t).Image g = image₂ f' (t.Image g') s :=
  coe_injective <| by
    push_cast
    exact image_image2_antidistrib_left h_antidistrib

/-- Symmetric of `finset.image_image₂_right_anticomm`. -/
theorem image_image₂_antidistrib_right {g : γ → δ} {f' : β → α' → δ} {g' : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' b (g' a)) : (image₂ f s t).Image g = image₂ f' t (s.Image g') :=
  coe_injective <| by
    push_cast
    exact image_image2_antidistrib_right h_antidistrib

/-- Symmetric of `finset.image_image₂_antidistrib_left`. -/
theorem image₂_image_left_anticomm {f : α' → β → γ} {g : α → α'} {f' : β → α → δ} {g' : δ → γ}
    (h_left_anticomm : ∀ a b, f (g a) b = g' (f' b a)) : image₂ f (s.Image g) t = (image₂ f' t s).Image g' :=
  (image_image₂_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm

/-- Symmetric of `finset.image_image₂_antidistrib_right`. -/
theorem image_image₂_right_anticomm {f : α → β' → γ} {g : β → β'} {f' : β → α → δ} {g' : δ → γ}
    (h_right_anticomm : ∀ a b, f a (g b) = g' (f' b a)) : image₂ f s (t.Image g) = (image₂ f' t s).Image g' :=
  (image_image₂_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm

end Finset

