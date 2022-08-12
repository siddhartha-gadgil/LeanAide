/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathbin.Algebra.Star.Basic
import Mathbin.Data.Set.Pointwise

/-!
# Pointwise star operation on sets

This file defines the star operation pointwise on sets and provides the basic API.
Besides basic facts about about how the star operation acts on sets (e.g., `(s ∩ t)⋆ = s⋆ ∩ t⋆`),
if `s t : set α`, then under suitable assumption on `α`, it is shown

* `(s + t)⋆ = s⋆ + t⋆`
* `(s * t)⋆ = t⋆ + s⋆`
* `(s⁻¹)⋆ = (s⋆)⁻¹`
-/


namespace Set

open Pointwise

-- mathport name: «expr ⋆»
local postfix:max "⋆" => star

variable {α : Type _} {s t : Set α} {a : α}

/-- The set `(star s : set α)` is defined as `{x | star x ∈ s}` in locale `pointwise`.
In the usual case where `star` is involutive, it is equal to `{star s | x ∈ s}`, see
`set.image_star`. -/
protected def hasStar [HasStar α] : HasStar (Set α) :=
  ⟨Preimage HasStar.star⟩

localized [Pointwise] attribute [instance] Set.hasStar

@[simp]
theorem star_empty [HasStar α] : (∅ : Set α)⋆ = ∅ :=
  rfl

@[simp]
theorem star_univ [HasStar α] : (Univ : Set α)⋆ = univ :=
  rfl

@[simp]
theorem nonempty_star [HasInvolutiveStar α] {s : Set α} : s⋆.Nonempty ↔ s.Nonempty :=
  star_involutive.Surjective.nonempty_preimage

theorem Nonempty.star [HasInvolutiveStar α] {s : Set α} (h : s.Nonempty) : s⋆.Nonempty :=
  nonempty_star.2 h

@[simp]
theorem mem_star [HasStar α] : a ∈ s⋆ ↔ a⋆ ∈ s :=
  Iff.rfl

theorem star_mem_star [HasInvolutiveStar α] : a⋆ ∈ s⋆ ↔ a ∈ s := by
  simp only [← mem_star, ← star_star]

@[simp]
theorem star_preimage [HasStar α] : HasStar.star ⁻¹' s = s⋆ :=
  rfl

@[simp]
theorem image_star [HasInvolutiveStar α] : HasStar.star '' s = s⋆ := by
  simp only [star_preimage]
  rw [image_eq_preimage_of_inverse] <;> intro <;> simp only [← star_star]

@[simp]
theorem inter_star [HasStar α] : (s ∩ t)⋆ = s⋆ ∩ t⋆ :=
  preimage_inter

@[simp]
theorem union_star [HasStar α] : (s ∪ t)⋆ = s⋆ ∪ t⋆ :=
  preimage_union

@[simp]
theorem Inter_star {ι : Sort _} [HasStar α] (s : ι → Set α) : (⋂ i, s i)⋆ = ⋂ i, (s i)⋆ :=
  preimage_Inter

@[simp]
theorem Union_star {ι : Sort _} [HasStar α] (s : ι → Set α) : (⋃ i, s i)⋆ = ⋃ i, (s i)⋆ :=
  preimage_Union

@[simp]
theorem compl_star [HasStar α] : (sᶜ)⋆ = s⋆ᶜ :=
  preimage_compl

@[simp]
instance [HasInvolutiveStar α] : HasInvolutiveStar (Set α) where
  star := HasStar.star
  star_involutive := fun s => by
    simp only [star_preimage, ← preimage_preimage, ← star_star, ← preimage_id']

@[simp]
theorem star_subset_star [HasInvolutiveStar α] {s t : Set α} : s⋆ ⊆ t⋆ ↔ s ⊆ t :=
  Equivₓ.star.Surjective.preimage_subset_preimage_iff

theorem star_subset [HasInvolutiveStar α] {s t : Set α} : s⋆ ⊆ t ↔ s ⊆ t⋆ := by
  rw [← star_subset_star, star_star]

theorem Finite.star [HasInvolutiveStar α] {s : Set α} (hs : s.Finite) : s⋆.Finite :=
  hs.Preimage <| star_injective.InjOn _

theorem star_singleton {β : Type _} [HasInvolutiveStar β] (x : β) : ({x} : Set β)⋆ = {x⋆} := by
  ext1 y
  rw [mem_star, mem_singleton_iff, mem_singleton_iff, star_eq_iff_star_eq, eq_comm]

protected theorem star_mul [Monoidₓ α] [StarSemigroup α] (s t : Set α) : (s * t)⋆ = t⋆ * s⋆ := by
  simp_rw [← image_star, ← image2_mul, image_image2, image2_image_left, image2_image_right, star_mul, image2_swap _ s t]

protected theorem star_add [AddMonoidₓ α] [StarAddMonoid α] (s t : Set α) : (s + t)⋆ = s⋆ + t⋆ := by
  simp_rw [← image_star, ← image2_add, image_image2, image2_image_left, image2_image_right, star_add]

@[simp]
instance [HasStar α] [HasTrivialStar α] :
    HasTrivialStar (Set α) where star_trivial := fun s => by
    rw [← star_preimage]
    ext1
    simp [← star_trivial]

protected theorem star_inv [Groupₓ α] [StarSemigroup α] (s : Set α) : s⁻¹⋆ = s⋆⁻¹ := by
  ext
  simp only [← mem_star, ← mem_inv, ← star_inv]

protected theorem star_inv' [DivisionRing α] [StarRing α] (s : Set α) : s⁻¹⋆ = s⋆⁻¹ := by
  ext
  simp only [← mem_star, ← mem_inv, ← star_inv']

end Set

