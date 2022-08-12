/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Data.Set.Finite
import Mathbin.GroupTheory.Submonoid.Basic

/-!
# Pointwise operations of sets

This file defines pointwise algebraic operations on sets.

## Main declarations

For sets `s` and `t` and scalar `a`:
* `s * t`: Multiplication, set of all `x * y` where `x ∈ s` and `y ∈ t`.
* `s + t`: Addition, set of all `x + y` where `x ∈ s` and `y ∈ t`.
* `s⁻¹`: Inversion, set of all `x⁻¹` where `x ∈ s`.
* `-s`: Negation, set of all `-x` where `x ∈ s`.
* `s / t`: Division, set of all `x / y` where `x ∈ s` and `y ∈ t`.
* `s - t`: Subtraction, set of all `x - y` where `x ∈ s` and `y ∈ t`.
* `s • t`: Scalar multiplication, set of all `x • y` where `x ∈ s` and `y ∈ t`.
* `s +ᵥ t`: Scalar addition, set of all `x +ᵥ y` where `x ∈ s` and `y ∈ t`.
* `s -ᵥ t`: Scalar subtraction, set of all `x -ᵥ y` where `x ∈ s` and `y ∈ t`.
* `a • s`: Scaling, set of all `a • x` where `x ∈ s`.
* `a +ᵥ s`: Translation, set of all `a +ᵥ x` where `x ∈ s`.

For `α` a semigroup/monoid, `set α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes

* The following expressions are considered in simp-normal form in a group:
  `(λ h, h * g) ⁻¹' s`, `(λ h, g * h) ⁻¹' s`, `(λ h, h * g⁻¹) ⁻¹' s`, `(λ h, g⁻¹ * h) ⁻¹' s`,
  `s * t`, `s⁻¹`, `(1 : set _)` (and similarly for additive variants).
  Expressions equal to one of these will be simplified.
* We put all instances in the locale `pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the locale to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/


library_note "pointwise nat action"/--
Pointwise monoids (`set`, `finset`, `filter`) have derived pointwise actions of the form
`has_smul α β → has_smul α (set β)`. When `α` is `ℕ` or `ℤ`, this action conflicts with the
nat or int action coming from `set β` being a `monoid` or `div_inv_monoid`. For example,
`2 • {a, b}` can both be `{2 • a, 2 • b}` (pointwise action, pointwise repeated addition,
`set.has_smul_set`) and `{a + a, a + b, b + a, b + b}` (nat or int action, repeated pointwise
addition, `set.has_nsmul`).

Because the pointwise action can easily be spelled out in such cases, we give higher priority to the
nat and int actions.
-/


open Function

variable {F α β γ : Type _}

namespace Set

/-! ### `0`/`1` as sets -/


section One

variable [One α] {s : Set α} {a : α}

/-- The set `1 : set α` is defined as `{1}` in locale `pointwise`. -/
@[to_additive "The set `0 : set α` is defined as `{0}` in locale `pointwise`."]
protected def hasOne : One (Set α) :=
  ⟨{1}⟩

localized [Pointwise] attribute [instance] Set.hasOne Set.hasZero

@[to_additive]
theorem singleton_one : ({1} : Set α) = 1 :=
  rfl

@[simp, to_additive]
theorem mem_one : a ∈ (1 : Set α) ↔ a = 1 :=
  Iff.rfl

@[to_additive]
theorem one_mem_one : (1 : α) ∈ (1 : Set α) :=
  Eq.refl _

@[simp, to_additive]
theorem one_subset : 1 ⊆ s ↔ (1 : α) ∈ s :=
  singleton_subset_iff

@[to_additive]
theorem one_nonempty : (1 : Set α).Nonempty :=
  ⟨1, rfl⟩

@[simp, to_additive]
theorem image_one {f : α → β} : f '' 1 = {f 1} :=
  image_singleton

@[to_additive]
theorem subset_one_iff_eq : s ⊆ 1 ↔ s = ∅ ∨ s = 1 :=
  subset_singleton_iff_eq

@[to_additive]
theorem Nonempty.subset_one_iff (h : s.Nonempty) : s ⊆ 1 ↔ s = 1 :=
  h.subset_singleton_iff

/-- The singleton operation as a `one_hom`. -/
@[to_additive "The singleton operation as a `zero_hom`."]
def singletonOneHom : OneHom α (Set α) :=
  ⟨singleton, singleton_one⟩

@[simp, to_additive]
theorem coe_singleton_one_hom : (singletonOneHom : α → Set α) = singleton :=
  rfl

end One

/-! ### Set negation/inversion -/


section Inv

/-- The pointwise inversion of set `s⁻¹` is defined as `{x | x⁻¹ ∈ s}` in locale `pointwise`. It i
equal to `{x⁻¹ | x ∈ s}`, see `set.image_inv`. -/
@[to_additive
      "The pointwise negation of set `-s` is defined as `{x | -x ∈ s}` in locale\n`pointwise`. It is equal to `{-x | x ∈ s}`, see `set.image_neg`."]
protected def hasInv [Inv α] : Inv (Set α) :=
  ⟨Preimage Inv.inv⟩

localized [Pointwise] attribute [instance] Set.hasInv Set.hasNeg

section Inv

variable {ι : Sort _} [Inv α] {s t : Set α} {a : α}

@[simp, to_additive]
theorem mem_inv : a ∈ s⁻¹ ↔ a⁻¹ ∈ s :=
  Iff.rfl

@[simp, to_additive]
theorem inv_preimage : Inv.inv ⁻¹' s = s⁻¹ :=
  rfl

@[simp, to_additive]
theorem inv_empty : (∅ : Set α)⁻¹ = ∅ :=
  rfl

@[simp, to_additive]
theorem inv_univ : (Univ : Set α)⁻¹ = univ :=
  rfl

@[simp, to_additive]
theorem inter_inv : (s ∩ t)⁻¹ = s⁻¹ ∩ t⁻¹ :=
  preimage_inter

@[simp, to_additive]
theorem union_inv : (s ∪ t)⁻¹ = s⁻¹ ∪ t⁻¹ :=
  preimage_union

@[simp, to_additive]
theorem Inter_inv (s : ι → Set α) : (⋂ i, s i)⁻¹ = ⋂ i, (s i)⁻¹ :=
  preimage_Inter

@[simp, to_additive]
theorem Union_inv (s : ι → Set α) : (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹ :=
  preimage_Union

@[simp, to_additive]
theorem compl_inv : (sᶜ)⁻¹ = s⁻¹ᶜ :=
  preimage_compl

end Inv

section HasInvolutiveInv

variable [HasInvolutiveInv α] {s t : Set α} {a : α}

@[to_additive]
theorem inv_mem_inv : a⁻¹ ∈ s⁻¹ ↔ a ∈ s := by
  simp only [← mem_inv, ← inv_invₓ]

@[simp, to_additive]
theorem nonempty_inv : s⁻¹.Nonempty ↔ s.Nonempty :=
  inv_involutive.Surjective.nonempty_preimage

@[to_additive]
theorem Nonempty.inv (h : s.Nonempty) : s⁻¹.Nonempty :=
  nonempty_inv.2 h

@[to_additive]
theorem Finite.inv (hs : s.Finite) : s⁻¹.Finite :=
  hs.Preimage <| inv_injective.InjOn _

@[simp, to_additive]
theorem image_inv : Inv.inv '' s = s⁻¹ :=
  congr_fun (image_eq_preimage_of_inverse inv_involutive.LeftInverse inv_involutive.RightInverse) _

@[simp, to_additive]
instance : HasInvolutiveInv (Set α) where
  inv := Inv.inv
  inv_inv := fun s => by
    simp only [inv_preimage, ← preimage_preimage, ← inv_invₓ, ← preimage_id']

@[simp, to_additive]
theorem inv_subset_inv : s⁻¹ ⊆ t⁻¹ ↔ s ⊆ t :=
  (Equivₓ.inv α).Surjective.preimage_subset_preimage_iff

@[to_additive]
theorem inv_subset : s⁻¹ ⊆ t ↔ s ⊆ t⁻¹ := by
  rw [← inv_subset_inv, inv_invₓ]

@[simp, to_additive]
theorem inv_singleton (a : α) : ({a} : Set α)⁻¹ = {a⁻¹} := by
  rw [← image_inv, image_singleton]

@[to_additive]
theorem inv_range {ι : Sort _} {f : ι → α} : (Range f)⁻¹ = Range fun i => (f i)⁻¹ := by
  rw [← image_inv]
  exact (range_comp _ _).symm

open MulOpposite

@[to_additive]
theorem image_op_inv : op '' s⁻¹ = (op '' s)⁻¹ := by
  simp_rw [← image_inv, Function.Semiconj.set_image op_inv s]

end HasInvolutiveInv

end Inv

open Pointwise

/-! ### Set addition/multiplication -/


section Mul

variable {ι : Sort _} {κ : ι → Sort _} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

/-- The pointwise multiplication of sets `s * t` and `t` is defined as `{x * y | x ∈ s, y ∈ t}` in
locale `pointwise`. -/
@[to_additive "The pointwise addition of sets `s + t` is defined as `{x + y | x ∈ s, y ∈ t}` in\nlocale `pointwise`."]
protected def hasMul : Mul (Set α) :=
  ⟨Image2 (· * ·)⟩

localized [Pointwise] attribute [instance] Set.hasMul Set.hasAdd

@[simp, to_additive]
theorem image2_mul : Image2 Mul.mul s t = s * t :=
  rfl

@[to_additive]
theorem mem_mul : a ∈ s * t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x * y = a :=
  Iff.rfl

@[to_additive]
theorem mul_mem_mul : a ∈ s → b ∈ t → a * b ∈ s * t :=
  mem_image2_of_mem

@[to_additive add_image_prod]
theorem image_mul_prod : (fun x : α × α => x.fst * x.snd) '' s ×ˢ t = s * t :=
  image_prod _

@[simp, to_additive]
theorem empty_mul : ∅ * s = ∅ :=
  image2_empty_left

@[simp, to_additive]
theorem mul_empty : s * ∅ = ∅ :=
  image2_empty_right

@[simp, to_additive]
theorem mul_eq_empty : s * t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff

@[simp, to_additive]
theorem mul_nonempty : (s * t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff

@[to_additive]
theorem Nonempty.mul : s.Nonempty → t.Nonempty → (s * t).Nonempty :=
  nonempty.image2

@[to_additive]
theorem Nonempty.of_mul_left : (s * t).Nonempty → s.Nonempty :=
  nonempty.of_image2_left

@[to_additive]
theorem Nonempty.of_mul_right : (s * t).Nonempty → t.Nonempty :=
  nonempty.of_image2_right

@[simp, to_additive]
theorem mul_singleton : s * {b} = (· * b) '' s :=
  image2_singleton_right

@[simp, to_additive]
theorem singleton_mul : {a} * t = (· * ·) a '' t :=
  image2_singleton_left

@[simp, to_additive]
theorem singleton_mul_singleton : ({a} : Set α) * {b} = {a * b} :=
  image2_singleton

@[to_additive, mono]
theorem mul_subset_mul : s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ * s₂ ⊆ t₁ * t₂ :=
  image2_subset

@[to_additive]
theorem mul_subset_mul_left : t₁ ⊆ t₂ → s * t₁ ⊆ s * t₂ :=
  image2_subset_left

@[to_additive]
theorem mul_subset_mul_right : s₁ ⊆ s₂ → s₁ * t ⊆ s₂ * t :=
  image2_subset_right

@[to_additive]
theorem mul_subset_iff : s * t ⊆ u ↔ ∀, ∀ x ∈ s, ∀, ∀ y ∈ t, ∀, x * y ∈ u :=
  image2_subset_iff

attribute [mono] add_subset_add

@[to_additive]
theorem union_mul : (s₁ ∪ s₂) * t = s₁ * t ∪ s₂ * t :=
  image2_union_left

@[to_additive]
theorem mul_union : s * (t₁ ∪ t₂) = s * t₁ ∪ s * t₂ :=
  image2_union_right

@[to_additive]
theorem inter_mul_subset : s₁ ∩ s₂ * t ⊆ s₁ * t ∩ (s₂ * t) :=
  image2_inter_subset_left

@[to_additive]
theorem mul_inter_subset : s * (t₁ ∩ t₂) ⊆ s * t₁ ∩ (s * t₂) :=
  image2_inter_subset_right

@[to_additive]
theorem Union_mul_left_image : (⋃ a ∈ s, (· * ·) a '' t) = s * t :=
  Union_image_left _

@[to_additive]
theorem Union_mul_right_image : (⋃ a ∈ t, (· * a) '' s) = s * t :=
  Union_image_right _

@[to_additive]
theorem Union_mul (s : ι → Set α) (t : Set α) : (⋃ i, s i) * t = ⋃ i, s i * t :=
  image2_Union_left _ _ _

@[to_additive]
theorem mul_Union (s : Set α) (t : ι → Set α) : (s * ⋃ i, t i) = ⋃ i, s * t i :=
  image2_Union_right _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[to_additive]
theorem Union₂_mul (s : ∀ i, κ i → Set α) (t : Set α) : (⋃ (i) (j), s i j) * t = ⋃ (i) (j), s i j * t :=
  image2_Union₂_left _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[to_additive]
theorem mul_Union₂ (s : Set α) (t : ∀ i, κ i → Set α) : (s * ⋃ (i) (j), t i j) = ⋃ (i) (j), s * t i j :=
  image2_Union₂_right _ _ _

@[to_additive]
theorem Inter_mul_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) * t ⊆ ⋂ i, s i * t :=
  image2_Inter_subset_left _ _ _

@[to_additive]
theorem mul_Inter_subset (s : Set α) (t : ι → Set α) : (s * ⋂ i, t i) ⊆ ⋂ i, s * t i :=
  image2_Inter_subset_right _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[to_additive]
theorem Inter₂_mul_subset (s : ∀ i, κ i → Set α) (t : Set α) : (⋂ (i) (j), s i j) * t ⊆ ⋂ (i) (j), s i j * t :=
  image2_Inter₂_subset_left _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[to_additive]
theorem mul_Inter₂_subset (s : Set α) (t : ∀ i, κ i → Set α) : (s * ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s * t i j :=
  image2_Inter₂_subset_right _ _ _

@[to_additive]
theorem Finite.mul : s.Finite → t.Finite → (s * t).Finite :=
  Finite.image2 _

/-- Multiplication preserves finiteness. -/
@[to_additive "Addition preserves finiteness."]
def fintypeMul [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] : Fintype (s * t : Set α) :=
  Set.fintypeImage2 _ _ _

/-- The singleton operation as a `mul_hom`. -/
@[to_additive "The singleton operation as an `add_hom`."]
def singletonMulHom : α →ₙ* Set α :=
  ⟨singleton, fun a b => singleton_mul_singleton.symm⟩

@[simp, to_additive]
theorem coe_singleton_mul_hom : (singletonMulHom : α → Set α) = singleton :=
  rfl

@[simp, to_additive]
theorem singleton_mul_hom_apply (a : α) : singletonMulHom a = {a} :=
  rfl

open MulOpposite

@[simp, to_additive]
theorem image_op_mul : op '' (s * t) = op '' t * op '' s :=
  image_image2_antidistrib op_mul

end Mul

/-! ### Set subtraction/division -/


section Div

variable {ι : Sort _} {κ : ι → Sort _} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

/-- The pointwise division of sets `s / t` is defined as `{x / y | x ∈ s, y ∈ t}` in locale
`pointwise`. -/
@[to_additive
      "The pointwise subtraction of sets `s - t` is defined as `{x - y | x ∈ s, y ∈ t}` in\nlocale `pointwise`."]
protected def hasDiv : Div (Set α) :=
  ⟨Image2 (· / ·)⟩

localized [Pointwise] attribute [instance] Set.hasDiv Set.hasSub

@[simp, to_additive]
theorem image2_div : Image2 Div.div s t = s / t :=
  rfl

@[to_additive]
theorem mem_div : a ∈ s / t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x / y = a :=
  Iff.rfl

@[to_additive]
theorem div_mem_div : a ∈ s → b ∈ t → a / b ∈ s / t :=
  mem_image2_of_mem

@[to_additive add_image_prod]
theorem image_div_prod : (fun x : α × α => x.fst / x.snd) '' s ×ˢ t = s / t :=
  image_prod _

@[simp, to_additive]
theorem empty_div : ∅ / s = ∅ :=
  image2_empty_left

@[simp, to_additive]
theorem div_empty : s / ∅ = ∅ :=
  image2_empty_right

@[simp, to_additive]
theorem div_eq_empty : s / t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff

@[simp, to_additive]
theorem div_nonempty : (s / t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff

@[to_additive]
theorem Nonempty.div : s.Nonempty → t.Nonempty → (s / t).Nonempty :=
  nonempty.image2

@[to_additive]
theorem Nonempty.of_div_left : (s / t).Nonempty → s.Nonempty :=
  nonempty.of_image2_left

@[to_additive]
theorem Nonempty.of_div_right : (s / t).Nonempty → t.Nonempty :=
  nonempty.of_image2_right

@[simp, to_additive]
theorem div_singleton : s / {b} = (· / b) '' s :=
  image2_singleton_right

@[simp, to_additive]
theorem singleton_div : {a} / t = (· / ·) a '' t :=
  image2_singleton_left

@[simp, to_additive]
theorem singleton_div_singleton : ({a} : Set α) / {b} = {a / b} :=
  image2_singleton

@[to_additive, mono]
theorem div_subset_div : s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ / s₂ ⊆ t₁ / t₂ :=
  image2_subset

@[to_additive]
theorem div_subset_div_left : t₁ ⊆ t₂ → s / t₁ ⊆ s / t₂ :=
  image2_subset_left

@[to_additive]
theorem div_subset_div_right : s₁ ⊆ s₂ → s₁ / t ⊆ s₂ / t :=
  image2_subset_right

@[to_additive]
theorem div_subset_iff : s / t ⊆ u ↔ ∀, ∀ x ∈ s, ∀, ∀ y ∈ t, ∀, x / y ∈ u :=
  image2_subset_iff

attribute [mono] sub_subset_sub

@[to_additive]
theorem union_div : (s₁ ∪ s₂) / t = s₁ / t ∪ s₂ / t :=
  image2_union_left

@[to_additive]
theorem div_union : s / (t₁ ∪ t₂) = s / t₁ ∪ s / t₂ :=
  image2_union_right

@[to_additive]
theorem inter_div_subset : s₁ ∩ s₂ / t ⊆ s₁ / t ∩ (s₂ / t) :=
  image2_inter_subset_left

@[to_additive]
theorem div_inter_subset : s / (t₁ ∩ t₂) ⊆ s / t₁ ∩ (s / t₂) :=
  image2_inter_subset_right

@[to_additive]
theorem Union_div_left_image : (⋃ a ∈ s, (· / ·) a '' t) = s / t :=
  Union_image_left _

@[to_additive]
theorem Union_div_right_image : (⋃ a ∈ t, (· / a) '' s) = s / t :=
  Union_image_right _

@[to_additive]
theorem Union_div (s : ι → Set α) (t : Set α) : (⋃ i, s i) / t = ⋃ i, s i / t :=
  image2_Union_left _ _ _

@[to_additive]
theorem div_Union (s : Set α) (t : ι → Set α) : (s / ⋃ i, t i) = ⋃ i, s / t i :=
  image2_Union_right _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[to_additive]
theorem Union₂_div (s : ∀ i, κ i → Set α) (t : Set α) : (⋃ (i) (j), s i j) / t = ⋃ (i) (j), s i j / t :=
  image2_Union₂_left _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[to_additive]
theorem div_Union₂ (s : Set α) (t : ∀ i, κ i → Set α) : (s / ⋃ (i) (j), t i j) = ⋃ (i) (j), s / t i j :=
  image2_Union₂_right _ _ _

@[to_additive]
theorem Inter_div_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) / t ⊆ ⋂ i, s i / t :=
  image2_Inter_subset_left _ _ _

@[to_additive]
theorem div_Inter_subset (s : Set α) (t : ι → Set α) : (s / ⋂ i, t i) ⊆ ⋂ i, s / t i :=
  image2_Inter_subset_right _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[to_additive]
theorem Inter₂_div_subset (s : ∀ i, κ i → Set α) (t : Set α) : (⋂ (i) (j), s i j) / t ⊆ ⋂ (i) (j), s i j / t :=
  image2_Inter₂_subset_left _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[to_additive]
theorem div_Inter₂_subset (s : Set α) (t : ∀ i, κ i → Set α) : (s / ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s / t i j :=
  image2_Inter₂_subset_right _ _ _

end Div

open Pointwise

/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `finset`. See
note [pointwise nat action].-/
protected def hasNsmul [Zero α] [Add α] : HasSmul ℕ (Set α) :=
  ⟨nsmulRec⟩

/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`set`. See note [pointwise nat action]. -/
@[to_additive]
protected def hasNpow [One α] [Mul α] : Pow (Set α) ℕ :=
  ⟨fun s n => npowRec n s⟩

/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `set`. See note [pointwise nat action]. -/
protected def hasZsmul [Zero α] [Add α] [Neg α] : HasSmul ℤ (Set α) :=
  ⟨zsmulRec⟩

/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `set`. See note [pointwise nat action]. -/
@[to_additive]
protected def hasZpow [One α] [Mul α] [Inv α] : Pow (Set α) ℤ :=
  ⟨fun s n => zpowRec n s⟩

localized [Pointwise] attribute [instance] Set.hasNsmul Set.hasNpow Set.hasZsmul Set.hasZpow

/-- `set α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_semigroup` under pointwise operations if `α` is."]
protected def semigroup [Semigroupₓ α] : Semigroupₓ (Set α) :=
  { Set.hasMul with mul_assoc := fun _ _ _ => image2_assoc mul_assoc }

/-- `set α` is a `comm_semigroup` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_comm_semigroup` under pointwise operations if `α` is."]
protected def commSemigroup [CommSemigroupₓ α] : CommSemigroupₓ (Set α) :=
  { Set.semigroup with mul_comm := fun s t => image2_comm mul_comm }

section MulOneClassₓ

variable [MulOneClassₓ α]

/-- `set α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_zero_class` under pointwise operations if `α` is."]
protected def mulOneClass : MulOneClassₓ (Set α) :=
  { Set.hasOne, Set.hasMul with
    mul_one := fun s => by
      simp only [singleton_one, ← mul_singleton, ← mul_oneₓ, ← image_id'],
    one_mul := fun s => by
      simp only [singleton_one, ← singleton_mul, ← one_mulₓ, ← image_id'] }

localized [Pointwise]
  attribute [instance]
    Set.mulOneClass Set.addZeroClass Set.semigroup Set.addSemigroup Set.commSemigroup Set.addCommSemigroup

@[to_additive]
theorem subset_mul_left (s : Set α) {t : Set α} (ht : (1 : α) ∈ t) : s ⊆ s * t := fun x hx => ⟨x, 1, hx, ht, mul_oneₓ _⟩

@[to_additive]
theorem subset_mul_right {s : Set α} (t : Set α) (hs : (1 : α) ∈ s) : t ⊆ s * t := fun x hx =>
  ⟨1, x, hs, hx, one_mulₓ _⟩

/-- The singleton operation as a `monoid_hom`. -/
@[to_additive "The singleton operation as an `add_monoid_hom`."]
def singletonMonoidHom : α →* Set α :=
  { singletonMulHom, singletonOneHom with }

@[simp, to_additive]
theorem coe_singleton_monoid_hom : (singletonMonoidHom : α → Set α) = singleton :=
  rfl

@[simp, to_additive]
theorem singleton_monoid_hom_apply (a : α) : singletonMonoidHom a = {a} :=
  rfl

end MulOneClassₓ

section Monoidₓ

variable [Monoidₓ α] {s t : Set α} {a : α} {m n : ℕ}

/-- `set α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_monoid` under pointwise operations if `α` is."]
protected def monoid : Monoidₓ (Set α) :=
  { Set.semigroup, Set.mulOneClass, Set.hasNpow with }

localized [Pointwise] attribute [instance] Set.monoid Set.addMonoid

@[to_additive]
instance decidableMemMul [Fintype α] [DecidableEq α] [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    DecidablePred (· ∈ s * t) := fun _ => decidableOfIff _ mem_mul.symm

@[to_additive]
instance decidableMemPow [Fintype α] [DecidableEq α] [DecidablePred (· ∈ s)] (n : ℕ) : DecidablePred (· ∈ s ^ n) := by
  induction' n with n ih
  · simp_rw [pow_zeroₓ, mem_one]
    infer_instance
    
  · let this := ih
    rw [pow_succₓ]
    infer_instance
    

@[to_additive]
theorem pow_mem_pow (ha : a ∈ s) : ∀ n : ℕ, a ^ n ∈ s ^ n
  | 0 => by
    rw [pow_zeroₓ]
    exact one_mem_one
  | n + 1 => by
    rw [pow_succₓ]
    exact mul_mem_mul ha (pow_mem_pow _)

@[to_additive]
theorem pow_subset_pow (hst : s ⊆ t) : ∀ n : ℕ, s ^ n ⊆ t ^ n
  | 0 => by
    rw [pow_zeroₓ]
    exact subset.rfl
  | n + 1 => by
    rw [pow_succₓ]
    exact mul_subset_mul hst (pow_subset_pow _)

@[to_additive]
theorem pow_subset_pow_of_one_mem (hs : (1 : α) ∈ s) : m ≤ n → s ^ m ⊆ s ^ n := by
  refine' Nat.le_induction _ (fun n h ih => _) _
  · exact subset.rfl
    
  · rw [pow_succₓ]
    exact ih.trans (subset_mul_right _ hs)
    

@[simp, to_additive]
theorem empty_pow {n : ℕ} (hn : n ≠ 0) : (∅ : Set α) ^ n = ∅ := by
  rw [← tsub_add_cancel_of_le (Nat.succ_le_of_ltₓ <| Nat.pos_of_ne_zeroₓ hn), pow_succₓ, empty_mul]

@[to_additive]
theorem mul_univ_of_one_mem (hs : (1 : α) ∈ s) : s * univ = univ :=
  eq_univ_iff_forall.2 fun a => mem_mul.2 ⟨_, _, hs, mem_univ _, one_mulₓ _⟩

@[to_additive]
theorem univ_mul_of_one_mem (ht : (1 : α) ∈ t) : univ * t = univ :=
  eq_univ_iff_forall.2 fun a => mem_mul.2 ⟨_, _, mem_univ _, ht, mul_oneₓ _⟩

@[simp, to_additive]
theorem univ_mul_univ : (Univ : Set α) * univ = univ :=
  mul_univ_of_one_mem <| mem_univ _

--TODO: `to_additive` trips up on the `1 : ℕ` used in the pattern-matching.
@[simp]
theorem nsmul_univ {α : Type _} [AddMonoidₓ α] : ∀ {n : ℕ}, n ≠ 0 → n • (Univ : Set α) = univ
  | 0 => fun h => (h rfl).elim
  | 1 => fun _ => one_nsmul _
  | n + 2 => fun _ => by
    rw [succ_nsmul, nsmul_univ n.succ_ne_zero, univ_add_univ]

@[simp, to_additive nsmul_univ]
theorem univ_pow : ∀ {n : ℕ}, n ≠ 0 → (Univ : Set α) ^ n = univ
  | 0 => fun h => (h rfl).elim
  | 1 => fun _ => pow_oneₓ _
  | n + 2 => fun _ => by
    rw [pow_succₓ, univ_pow n.succ_ne_zero, univ_mul_univ]

@[to_additive]
protected theorem _root_.is_unit.set : IsUnit a → IsUnit ({a} : Set α) :=
  IsUnit.map (singletonMonoidHom : α →* Set α)

end Monoidₓ

/-- `set α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_comm_monoid` under pointwise operations if `α` is."]
protected def commMonoid [CommMonoidₓ α] : CommMonoidₓ (Set α) :=
  { Set.monoid, Set.commSemigroup with }

localized [Pointwise] attribute [instance] Set.commMonoid Set.addCommMonoid

open Pointwise

section DivisionMonoid

variable [DivisionMonoid α] {s t : Set α}

@[to_additive]
protected theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1 := by
  refine' ⟨fun h => _, _⟩
  · have hst : (s * t).Nonempty := h.symm.subst one_nonempty
    obtain ⟨a, ha⟩ := hst.of_image2_left
    obtain ⟨b, hb⟩ := hst.of_image2_right
    have H : ∀ {a b}, a ∈ s → b ∈ t → a * b = (1 : α) := fun a b ha hb => h.subset <| mem_image2_of_mem ha hb
    refine' ⟨a, b, _, _, H ha hb⟩ <;> refine' eq_singleton_iff_unique_mem.2 ⟨‹_›, fun x hx => _⟩
    · exact (eq_inv_of_mul_eq_one_left <| H hx hb).trans (inv_eq_of_mul_eq_one_left <| H ha hb)
      
    · exact (eq_inv_of_mul_eq_one_right <| H ha hx).trans (inv_eq_of_mul_eq_one_right <| H ha hb)
      
    
  · rintro ⟨b, c, rfl, rfl, h⟩
    rw [singleton_mul_singleton, h, singleton_one]
    

/-- `set α` is a division monoid under pointwise operations if `α` is. -/
@[to_additive SubtractionMonoid "`set α` is a subtraction monoid under pointwise operations if `α`\nis."]
protected def divisionMonoid : DivisionMonoid (Set α) :=
  { Set.monoid, Set.hasInvolutiveInv, Set.hasDiv, Set.hasZpow with
    mul_inv_rev := fun s t => by
      simp_rw [← image_inv]
      exact image_image2_antidistrib mul_inv_rev,
    inv_eq_of_mul := fun s t h => by
      obtain ⟨a, b, rfl, rfl, hab⟩ := Set.mul_eq_one_iff.1 h
      rw [inv_singleton, inv_eq_of_mul_eq_one_right hab],
    div_eq_mul_inv := fun s t => by
      rw [← image_id (s / t), ← image_inv]
      exact image_image2_distrib_right div_eq_mul_inv }

@[simp, to_additive]
theorem is_unit_iff : IsUnit s ↔ ∃ a, s = {a} ∧ IsUnit a := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, b, ha, hb, h⟩ := Set.mul_eq_one_iff.1 u.mul_inv
    refine' ⟨a, ha, ⟨a, b, h, singleton_injective _⟩, rfl⟩
    rw [← singleton_mul_singleton, ← ha, ← hb]
    exact u.inv_mul
    
  · rintro ⟨a, rfl, ha⟩
    exact ha.set
    

end DivisionMonoid

/-- `set α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive SubtractionCommMonoid
      "`set α` is a commutative subtraction monoid under pointwise\noperations if `α` is."]
protected def divisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid (Set α) :=
  { Set.divisionMonoid, Set.commSemigroup with }

/-- `set α` has distributive negation if `α` has. -/
protected def hasDistribNeg [Mul α] [HasDistribNeg α] : HasDistribNeg (Set α) :=
  { Set.hasInvolutiveNeg with
    neg_mul := fun _ _ => by
      simp_rw [← image_neg]
      exact image2_image_left_comm neg_mul,
    mul_neg := fun _ _ => by
      simp_rw [← image_neg]
      exact image_image2_right_comm mul_neg }

localized [Pointwise]
  attribute [instance]
    Set.divisionMonoid Set.subtractionMonoid Set.divisionCommMonoid Set.subtractionCommMonoid Set.hasDistribNeg

section Distribₓ

variable [Distribₓ α] (s t u : Set α)

/-!
Note that `set α` is not a `distrib` because `s * t + s * u` has cross terms that `s * (t + u)`
lacks.
-/


theorem mul_add_subset : s * (t + u) ⊆ s * t + s * u :=
  image2_distrib_subset_left mul_addₓ

theorem add_mul_subset : (s + t) * u ⊆ s * u + t * u :=
  image2_distrib_subset_right add_mulₓ

end Distribₓ

section MulZeroClassₓ

variable [MulZeroClassₓ α] {s t : Set α}

/-! Note that `set` is not a `mul_zero_class` because `0 * ∅ ≠ 0`. -/


theorem mul_zero_subset (s : Set α) : s * 0 ⊆ 0 := by
  simp [← subset_def, ← mem_mul]

theorem zero_mul_subset (s : Set α) : 0 * s ⊆ 0 := by
  simp [← subset_def, ← mem_mul]

theorem Nonempty.mul_zero (hs : s.Nonempty) : s * 0 = 0 :=
  s.mul_zero_subset.antisymm <| by
    simpa [← mem_mul] using hs

theorem Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 :=
  s.zero_mul_subset.antisymm <| by
    simpa [← mem_mul] using hs

end MulZeroClassₓ

section Groupₓ

variable [Groupₓ α] {s t : Set α} {a b : α}

/-! Note that `set` is not a `group` because `s / s ≠ 1` in general. -/


@[simp, to_additive]
theorem one_mem_div_iff : (1 : α) ∈ s / t ↔ ¬Disjoint s t := by
  simp [← not_disjoint_iff_nonempty_inter, ← mem_div, ← div_eq_one, ← Set.Nonempty]

@[to_additive]
theorem not_one_mem_div_iff : (1 : α) ∉ s / t ↔ Disjoint s t :=
  one_mem_div_iff.not_left

alias not_one_mem_div_iff ↔ _ _root_.disjoint.one_not_mem_div_set

attribute [to_additive] Disjoint.one_not_mem_div_set

@[to_additive]
theorem Nonempty.one_mem_div (h : s.Nonempty) : (1 : α) ∈ s / s :=
  let ⟨a, ha⟩ := h
  mem_div.2 ⟨a, a, ha, ha, div_self' _⟩

@[to_additive]
theorem is_unit_singleton (a : α) : IsUnit ({a} : Set α) :=
  (Groupₓ.is_unit a).Set

@[simp, to_additive]
theorem is_unit_iff_singleton : IsUnit s ↔ ∃ a, s = {a} := by
  simp only [← is_unit_iff, ← Groupₓ.is_unit, ← and_trueₓ]

@[simp, to_additive]
theorem image_mul_left : (· * ·) a '' t = (· * ·) a⁻¹ ⁻¹' t := by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

@[simp, to_additive]
theorem image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t := by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp

@[to_additive]
theorem image_mul_left' : (fun b => a⁻¹ * b) '' t = (fun b => a * b) ⁻¹' t := by
  simp

@[to_additive]
theorem image_mul_right' : (· * b⁻¹) '' t = (· * b) ⁻¹' t := by
  simp

@[simp, to_additive]
theorem preimage_mul_left_singleton : (· * ·) a ⁻¹' {b} = {a⁻¹ * b} := by
  rw [← image_mul_left', image_singleton]

@[simp, to_additive]
theorem preimage_mul_right_singleton : (· * a) ⁻¹' {b} = {b * a⁻¹} := by
  rw [← image_mul_right', image_singleton]

@[simp, to_additive]
theorem preimage_mul_left_one : (· * ·) a ⁻¹' 1 = {a⁻¹} := by
  rw [← image_mul_left', image_one, mul_oneₓ]

@[simp, to_additive]
theorem preimage_mul_right_one : (· * b) ⁻¹' 1 = {b⁻¹} := by
  rw [← image_mul_right', image_one, one_mulₓ]

@[to_additive]
theorem preimage_mul_left_one' : (fun b => a⁻¹ * b) ⁻¹' 1 = {a} := by
  simp

@[to_additive]
theorem preimage_mul_right_one' : (· * b⁻¹) ⁻¹' 1 = {b} := by
  simp

@[simp, to_additive]
theorem mul_univ (hs : s.Nonempty) : s * (Univ : Set α) = univ :=
  let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, a⁻¹ * b, ha, trivialₓ, mul_inv_cancel_left _ _⟩

@[simp, to_additive]
theorem univ_mul (ht : t.Nonempty) : (Univ : Set α) * t = univ :=
  let ⟨a, ha⟩ := ht
  eq_univ_of_forall fun b => ⟨b * a⁻¹, a, trivialₓ, ha, inv_mul_cancel_right _ _⟩

end Groupₓ

section GroupWithZeroₓ

variable [GroupWithZeroₓ α] {s t : Set α}

theorem div_zero_subset (s : Set α) : s / 0 ⊆ 0 := by
  simp [← subset_def, ← mem_div]

theorem zero_div_subset (s : Set α) : 0 / s ⊆ 0 := by
  simp [← subset_def, ← mem_div]

theorem Nonempty.div_zero (hs : s.Nonempty) : s / 0 = 0 :=
  s.div_zero_subset.antisymm <| by
    simpa [← mem_div] using hs

theorem Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 :=
  s.zero_div_subset.antisymm <| by
    simpa [← mem_div] using hs

end GroupWithZeroₓ

section Mul

variable [Mul α] [Mul β] [MulHomClass F α β] (m : F) {s t : Set α}

include α β

@[to_additive]
theorem image_mul : m '' (s * t) = m '' s * m '' t :=
  image_image2_distrib <| map_mul m

@[to_additive]
theorem preimage_mul_preimage_subset {s t : Set β} : m ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) := by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, _, ‹_›, ‹_›, (map_mul m _ _).symm⟩

end Mul

section Groupₓ

variable [Groupₓ α] [DivisionMonoid β] [MonoidHomClass F α β] (m : F) {s t : Set α}

include α β

@[to_additive]
theorem image_div : m '' (s / t) = m '' s / m '' t :=
  image_image2_distrib <| map_div m

@[to_additive]
theorem preimage_div_preimage_subset {s t : Set β} : m ⁻¹' s / m ⁻¹' t ⊆ m ⁻¹' (s / t) := by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, _, ‹_›, ‹_›, (map_div m _ _).symm⟩

end Groupₓ

@[to_additive]
theorem bdd_above_mul [OrderedCommMonoid α] {A B : Set α} : BddAbove A → BddAbove B → BddAbove (A * B) := by
  rintro ⟨bA, hbA⟩ ⟨bB, hbB⟩
  use bA * bB
  rintro x ⟨xa, xb, hxa, hxb, rfl⟩
  exact mul_le_mul' (hbA hxa) (hbB hxb)

open Pointwise

section BigOperators

open BigOperators

variable {ι : Type _} [CommMonoidₓ α]

/-- The n-ary version of `set.mem_mul`. -/
@[to_additive " The n-ary version of `set.mem_add`. "]
theorem mem_finset_prod (t : Finset ι) (f : ι → Set α) (a : α) :
    (a ∈ ∏ i in t, f i) ↔ ∃ (g : ι → α)(hg : ∀ {i}, i ∈ t → g i ∈ f i), (∏ i in t, g i) = a := by
  classical
  induction' t using Finset.induction_on with i is hi ih generalizing a
  · simp_rw [Finset.prod_empty, Set.mem_one]
    exact ⟨fun h => ⟨fun i => a, fun i => False.elim, h.symm⟩, fun ⟨f, _, hf⟩ => hf.symm⟩
    
  rw [Finset.prod_insert hi, Set.mem_mul]
  simp_rw [Finset.prod_insert hi]
  simp_rw [ih]
  constructor
  · rintro ⟨x, y, hx, ⟨g, hg, rfl⟩, rfl⟩
    refine' ⟨Function.update g i x, fun j hj => _, _⟩
    obtain rfl | hj := finset.mem_insert.mp hj
    · rw [Function.update_same]
      exact hx
      
    · rw [update_noteq (ne_of_mem_of_not_mem hj hi)]
      exact hg hj
      
    rw [Finset.prod_update_of_not_mem hi, Function.update_same]
    
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g i, is.prod g, hg (is.mem_insert_self _), ⟨g, fun i hi => hg (Finset.mem_insert_of_mem hi), rfl⟩, rfl⟩
    

/-- A version of `set.mem_finset_prod` with a simpler RHS for products over a fintype. -/
@[to_additive " A version of `set.mem_finset_sum` with a simpler RHS for sums over a fintype. "]
theorem mem_fintype_prod [Fintype ι] (f : ι → Set α) (a : α) :
    (a ∈ ∏ i, f i) ↔ ∃ (g : ι → α)(hg : ∀ i, g i ∈ f i), (∏ i, g i) = a := by
  rw [mem_finset_prod]
  simp

/-- An n-ary version of `set.mul_mem_mul`. -/
@[to_additive " An n-ary version of `set.add_mem_add`. "]
theorem list_prod_mem_list_prod (t : List ι) (f : ι → Set α) (g : ι → α) (hg : ∀, ∀ i ∈ t, ∀, g i ∈ f i) :
    (t.map g).Prod ∈ (t.map f).Prod := by
  induction' t with h tl ih
  · simp_rw [List.map_nil, List.prod_nil, Set.mem_one]
    
  · simp_rw [List.map_cons, List.prod_cons]
    exact mul_mem_mul (hg h <| List.mem_cons_selfₓ _ _) (ih fun i hi => hg i <| List.mem_cons_of_memₓ _ hi)
    

/-- An n-ary version of `set.mul_subset_mul`. -/
@[to_additive " An n-ary version of `set.add_subset_add`. "]
theorem list_prod_subset_list_prod (t : List ι) (f₁ f₂ : ι → Set α) (hf : ∀, ∀ i ∈ t, ∀, f₁ i ⊆ f₂ i) :
    (t.map f₁).Prod ⊆ (t.map f₂).Prod := by
  induction' t with h tl ih
  · rfl
    
  · simp_rw [List.map_cons, List.prod_cons]
    exact mul_subset_mul (hf h <| List.mem_cons_selfₓ _ _) (ih fun i hi => hf i <| List.mem_cons_of_memₓ _ hi)
    

@[to_additive]
theorem list_prod_singleton {M : Type _} [CommMonoidₓ M] (s : List M) :
    (s.map fun i => ({i} : Set M)).Prod = {s.Prod} :=
  (map_list_prod (singletonMonoidHom : M →* Set M) _).symm

/-- An n-ary version of `set.mul_mem_mul`. -/
@[to_additive " An n-ary version of `set.add_mem_add`. "]
theorem multiset_prod_mem_multiset_prod (t : Multiset ι) (f : ι → Set α) (g : ι → α) (hg : ∀, ∀ i ∈ t, ∀, g i ∈ f i) :
    (t.map g).Prod ∈ (t.map f).Prod := by
  induction t using Quotientₓ.induction_on
  simp_rw [Multiset.quot_mk_to_coe, Multiset.coe_map, Multiset.coe_prod]
  exact list_prod_mem_list_prod _ _ _ hg

/-- An n-ary version of `set.mul_subset_mul`. -/
@[to_additive " An n-ary version of `set.add_subset_add`. "]
theorem multiset_prod_subset_multiset_prod (t : Multiset ι) (f₁ f₂ : ι → Set α) (hf : ∀, ∀ i ∈ t, ∀, f₁ i ⊆ f₂ i) :
    (t.map f₁).Prod ⊆ (t.map f₂).Prod := by
  induction t using Quotientₓ.induction_on
  simp_rw [Multiset.quot_mk_to_coe, Multiset.coe_map, Multiset.coe_prod]
  exact list_prod_subset_list_prod _ _ _ hf

@[to_additive]
theorem multiset_prod_singleton {M : Type _} [CommMonoidₓ M] (s : Multiset M) :
    (s.map fun i => ({i} : Set M)).Prod = {s.Prod} :=
  (map_multiset_prod (singletonMonoidHom : M →* Set M) _).symm

/-- An n-ary version of `set.mul_mem_mul`. -/
@[to_additive " An n-ary version of `set.add_mem_add`. "]
theorem finset_prod_mem_finset_prod (t : Finset ι) (f : ι → Set α) (g : ι → α) (hg : ∀, ∀ i ∈ t, ∀, g i ∈ f i) :
    (∏ i in t, g i) ∈ ∏ i in t, f i :=
  multiset_prod_mem_multiset_prod _ _ _ hg

/-- An n-ary version of `set.mul_subset_mul`. -/
@[to_additive " An n-ary version of `set.add_subset_add`. "]
theorem finset_prod_subset_finset_prod (t : Finset ι) (f₁ f₂ : ι → Set α) (hf : ∀, ∀ i ∈ t, ∀, f₁ i ⊆ f₂ i) :
    (∏ i in t, f₁ i) ⊆ ∏ i in t, f₂ i :=
  multiset_prod_subset_multiset_prod _ _ _ hf

@[to_additive]
theorem finset_prod_singleton {M ι : Type _} [CommMonoidₓ M] (s : Finset ι) (I : ι → M) :
    (∏ i : ι in s, ({I i} : Set M)) = {∏ i : ι in s, I i} :=
  (map_prod (singletonMonoidHom : M →* Set M) _ _).symm

/-! TODO: define `decidable_mem_finset_prod` and `decidable_mem_finset_sum`. -/


end BigOperators

/-! ### Translation/scaling of sets -/


section Smul

/-- The dilation of set `x • s` is defined as `{x • y | y ∈ s}` in locale `pointwise`. -/
@[to_additive "The translation of set `x +ᵥ s` is defined as `{x +ᵥ y | y ∈ s}` in\nlocale `pointwise`."]
protected def hasSmulSet [HasSmul α β] : HasSmul α (Set β) :=
  ⟨fun a => Image (HasSmul.smul a)⟩

/-- The pointwise scalar multiplication of sets `s • t` is defined as `{x • y | x ∈ s, y ∈ t}` in
locale `pointwise`. -/
@[to_additive
      "The pointwise scalar addition of sets `s +ᵥ t` is defined as\n`{x +ᵥ y | x ∈ s, y ∈ t}` in locale `pointwise`."]
protected def hasSmul [HasSmul α β] : HasSmul (Set α) (Set β) :=
  ⟨Image2 HasSmul.smul⟩

localized [Pointwise] attribute [instance] Set.hasSmulSet Set.hasSmul

localized [Pointwise] attribute [instance] Set.hasVaddSet Set.hasVadd

section HasSmul

variable {ι : Sort _} {κ : ι → Sort _} [HasSmul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α} {b : β}

@[simp, to_additive]
theorem image2_smul : Image2 HasSmul.smul s t = s • t :=
  rfl

@[to_additive add_image_prod]
theorem image_smul_prod : (fun x : α × β => x.fst • x.snd) '' s ×ˢ t = s • t :=
  image_prod _

@[to_additive]
theorem mem_smul : b ∈ s • t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x • y = b :=
  Iff.rfl

@[to_additive]
theorem smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t :=
  mem_image2_of_mem

@[simp, to_additive]
theorem empty_smul : (∅ : Set α) • t = ∅ :=
  image2_empty_left

@[simp, to_additive]
theorem smul_empty : s • (∅ : Set β) = ∅ :=
  image2_empty_right

@[simp, to_additive]
theorem smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff

@[simp, to_additive]
theorem smul_nonempty : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff

@[to_additive]
theorem Nonempty.smul : s.Nonempty → t.Nonempty → (s • t).Nonempty :=
  nonempty.image2

@[to_additive]
theorem Nonempty.of_smul_left : (s • t).Nonempty → s.Nonempty :=
  nonempty.of_image2_left

@[to_additive]
theorem Nonempty.of_smul_right : (s • t).Nonempty → t.Nonempty :=
  nonempty.of_image2_right

@[simp, to_additive]
theorem smul_singleton : s • {b} = (· • b) '' s :=
  image2_singleton_right

@[simp, to_additive]
theorem singleton_smul : ({a} : Set α) • t = a • t :=
  image2_singleton_left

@[simp, to_additive]
theorem singleton_smul_singleton : ({a} : Set α) • ({b} : Set β) = {a • b} :=
  image2_singleton

@[to_additive, mono]
theorem smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ :=
  image2_subset

@[to_additive]
theorem smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ :=
  image2_subset_left

@[to_additive]
theorem smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t :=
  image2_subset_right

@[to_additive]
theorem smul_subset_iff : s • t ⊆ u ↔ ∀, ∀ a ∈ s, ∀, ∀ b ∈ t, ∀, a • b ∈ u :=
  image2_subset_iff

attribute [mono] vadd_subset_vadd

@[to_additive]
theorem union_smul : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t :=
  image2_union_left

@[to_additive]
theorem smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ :=
  image2_union_right

@[to_additive]
theorem inter_smul_subset : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t :=
  image2_inter_subset_left

@[to_additive]
theorem smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ :=
  image2_inter_subset_right

@[to_additive]
theorem Union_smul_left_image : (⋃ a ∈ s, a • t) = s • t :=
  Union_image_left _

@[to_additive]
theorem Union_smul_right_image : (⋃ a ∈ t, (· • a) '' s) = s • t :=
  Union_image_right _

@[to_additive]
theorem Union_smul (s : ι → Set α) (t : Set β) : (⋃ i, s i) • t = ⋃ i, s i • t :=
  image2_Union_left _ _ _

@[to_additive]
theorem smul_Union (s : Set α) (t : ι → Set β) : (s • ⋃ i, t i) = ⋃ i, s • t i :=
  image2_Union_right _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[to_additive]
theorem Union₂_smul (s : ∀ i, κ i → Set α) (t : Set β) : (⋃ (i) (j), s i j) • t = ⋃ (i) (j), s i j • t :=
  image2_Union₂_left _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[to_additive]
theorem smul_Union₂ (s : Set α) (t : ∀ i, κ i → Set β) : (s • ⋃ (i) (j), t i j) = ⋃ (i) (j), s • t i j :=
  image2_Union₂_right _ _ _

@[to_additive]
theorem Inter_smul_subset (s : ι → Set α) (t : Set β) : (⋂ i, s i) • t ⊆ ⋂ i, s i • t :=
  image2_Inter_subset_left _ _ _

@[to_additive]
theorem smul_Inter_subset (s : Set α) (t : ι → Set β) : (s • ⋂ i, t i) ⊆ ⋂ i, s • t i :=
  image2_Inter_subset_right _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[to_additive]
theorem Inter₂_smul_subset (s : ∀ i, κ i → Set α) (t : Set β) : (⋂ (i) (j), s i j) • t ⊆ ⋂ (i) (j), s i j • t :=
  image2_Inter₂_subset_left _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[to_additive]
theorem smul_Inter₂_subset (s : Set α) (t : ∀ i, κ i → Set β) : (s • ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s • t i j :=
  image2_Inter₂_subset_right _ _ _

@[to_additive]
theorem Finite.smul : s.Finite → t.Finite → (s • t).Finite :=
  Finite.image2 _

@[simp, to_additive]
theorem bUnion_smul_set (s : Set α) (t : Set β) : (⋃ a ∈ s, a • t) = s • t :=
  Union_image_left _

end HasSmul

section HasSmulSet

variable {ι : Sort _} {κ : ι → Sort _} [HasSmul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

@[simp, to_additive]
theorem image_smul : (fun x => a • x) '' t = a • t :=
  rfl

@[to_additive]
theorem mem_smul_set : x ∈ a • t ↔ ∃ y, y ∈ t ∧ a • y = x :=
  Iff.rfl

@[to_additive]
theorem smul_mem_smul_set : b ∈ s → a • b ∈ a • s :=
  mem_image_of_mem _

@[simp, to_additive]
theorem smul_set_empty : a • (∅ : Set β) = ∅ :=
  image_empty _

@[simp, to_additive]
theorem smul_set_eq_empty : a • s = ∅ ↔ s = ∅ :=
  image_eq_empty

@[simp, to_additive]
theorem smul_set_nonempty : (a • s).Nonempty ↔ s.Nonempty :=
  nonempty_image_iff

@[simp, to_additive]
theorem smul_set_singleton : a • ({b} : Set β) = {a • b} :=
  image_singleton

@[to_additive]
theorem smul_set_mono : s ⊆ t → a • s ⊆ a • t :=
  image_subset _

@[to_additive]
theorem smul_set_subset_iff : a • s ⊆ t ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ t :=
  image_subset_iff

@[to_additive]
theorem smul_set_union : a • (t₁ ∪ t₂) = a • t₁ ∪ a • t₂ :=
  image_union _ _ _

@[to_additive]
theorem smul_set_inter_subset : a • (t₁ ∩ t₂) ⊆ a • t₁ ∩ a • t₂ :=
  image_inter_subset _ _ _

@[to_additive]
theorem smul_set_Union (a : α) (s : ι → Set β) : (a • ⋃ i, s i) = ⋃ i, a • s i :=
  image_Union

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[to_additive]
theorem smul_set_Union₂ (a : α) (s : ∀ i, κ i → Set β) : (a • ⋃ (i) (j), s i j) = ⋃ (i) (j), a • s i j :=
  image_Union₂ _ _

@[to_additive]
theorem smul_set_Inter_subset (a : α) (t : ι → Set β) : (a • ⋂ i, t i) ⊆ ⋂ i, a • t i :=
  image_Inter_subset _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[to_additive]
theorem smul_set_Inter₂_subset (a : α) (t : ∀ i, κ i → Set β) : (a • ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), a • t i j :=
  image_Inter₂_subset _ _

@[to_additive]
theorem Nonempty.smul_set : s.Nonempty → (a • s).Nonempty :=
  Nonempty.image _

@[to_additive]
theorem Finite.smul_set : s.Finite → (a • s).Finite :=
  Finite.image _

end HasSmulSet

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {a : α} {b : β}

@[to_additive]
theorem smul_set_inter [Groupₓ α] [MulAction α β] {s t : Set β} : a • (s ∩ t) = a • s ∩ a • t :=
  (image_inter <| MulAction.injective a).symm

theorem smul_set_inter₀ [GroupWithZeroₓ α] [MulAction α β] {s t : Set β} (ha : a ≠ 0) : a • (s ∩ t) = a • s ∩ a • t :=
  show Units.mk0 a ha • _ = _ from smul_set_inter

@[simp, to_additive]
theorem smul_set_univ [Groupₓ α] [MulAction α β] {a : α} : a • (Univ : Set β) = univ :=
  eq_univ_of_forall fun b => ⟨a⁻¹ • b, trivialₓ, smul_inv_smul _ _⟩

@[simp, to_additive]
theorem smul_univ [Groupₓ α] [MulAction α β] {s : Set α} (hs : s.Nonempty) : s • (Univ : Set β) = univ :=
  let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, a⁻¹ • b, ha, trivialₓ, smul_inv_smul _ _⟩

@[to_additive]
theorem range_smul_range {ι κ : Type _} [HasSmul α β] (b : ι → α) (c : κ → β) :
    Range b • Range c = Range fun p : ι × κ => b p.1 • c p.2 :=
  ext fun x =>
    ⟨fun hx =>
      let ⟨p, q, ⟨i, hi⟩, ⟨j, hj⟩, hpq⟩ := Set.mem_smul.1 hx
      ⟨(i, j), hpq ▸ hi ▸ hj ▸ rfl⟩,
      fun ⟨⟨i, j⟩, h⟩ => Set.mem_smul.2 ⟨b i, c j, ⟨i, rfl⟩, ⟨j, rfl⟩, h⟩⟩

@[to_additive]
theorem smul_set_range [HasSmul α β] {ι : Sort _} {f : ι → β} : a • Range f = Range fun i => a • f i :=
  (range_comp _ _).symm

@[to_additive]
instance smul_comm_class_set [HasSmul α γ] [HasSmul β γ] [SmulCommClass α β γ] : SmulCommClass α β (Set γ) :=
  ⟨fun _ _ => commute.set_image <| smul_comm _ _⟩

@[to_additive]
instance smul_comm_class_set' [HasSmul α γ] [HasSmul β γ] [SmulCommClass α β γ] : SmulCommClass α (Set β) (Set γ) :=
  ⟨fun _ _ _ => image_image2_distrib_right <| smul_comm _⟩

@[to_additive]
instance smul_comm_class_set'' [HasSmul α γ] [HasSmul β γ] [SmulCommClass α β γ] : SmulCommClass (Set α) β (Set γ) :=
  have := SmulCommClass.symm α β γ
  SmulCommClass.symm _ _ _

@[to_additive]
instance smul_comm_class [HasSmul α γ] [HasSmul β γ] [SmulCommClass α β γ] : SmulCommClass (Set α) (Set β) (Set γ) :=
  ⟨fun _ _ _ => image2_left_comm smul_comm⟩

instance is_scalar_tower [HasSmul α β] [HasSmul α γ] [HasSmul β γ] [IsScalarTower α β γ] :
    IsScalarTower α β (Set γ) where smul_assoc := fun a b T => by
    simp only [image_smul, ← image_image, ← smul_assoc]

instance is_scalar_tower' [HasSmul α β] [HasSmul α γ] [HasSmul β γ] [IsScalarTower α β γ] :
    IsScalarTower α (Set β) (Set γ) :=
  ⟨fun _ _ _ => image2_image_left_comm <| smul_assoc _⟩

instance is_scalar_tower'' [HasSmul α β] [HasSmul α γ] [HasSmul β γ] [IsScalarTower α β γ] :
    IsScalarTower (Set α) (Set β) (Set γ) where smul_assoc := fun T T' T'' => image2_assoc smul_assoc

instance is_central_scalar [HasSmul α β] [HasSmul αᵐᵒᵖ β] [IsCentralScalar α β] : IsCentralScalar α (Set β) :=
  ⟨fun a S => (congr_arg fun f => f '' S) <| funext fun _ => op_smul_eq_smul _ _⟩

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of `set α`
on `set β`. -/
@[to_additive
      "An additive action of an additive monoid `α` on a type `β` gives an additive action\nof `set α` on `set β`"]
protected def mulAction [Monoidₓ α] [MulAction α β] : MulAction (Set α) (Set β) where
  mul_smul := fun _ _ _ => image2_assoc mul_smul
  one_smul := fun s =>
    image2_singleton_left.trans <| by
      simp_rw [one_smul, image_id']

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `set β`. -/
@[to_additive "An additive action of an additive monoid on a type `β` gives an additive action\non `set β`."]
protected def mulActionSet [Monoidₓ α] [MulAction α β] : MulAction α (Set β) where
  mul_smul := by
    intros
    simp only [image_smul, ← image_image, mul_smul]
  one_smul := by
    intros
    simp only [image_smul, ← one_smul, ← image_id']

localized [Pointwise] attribute [instance] Set.mulActionSet Set.addActionSet Set.mulAction Set.addAction

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `set β`. -/
protected def distribMulActionSet [Monoidₓ α] [AddMonoidₓ β] [DistribMulAction α β] : DistribMulAction α (Set β) where
  smul_add := fun _ _ _ => image_image2_distrib <| smul_add _
  smul_zero := fun _ =>
    image_singleton.trans <| by
      rw [smul_zero, singleton_zero]

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `set β`. -/
protected def mulDistribMulActionSet [Monoidₓ α] [Monoidₓ β] [MulDistribMulAction α β] :
    MulDistribMulAction α (Set β) where
  smul_mul := fun _ _ _ => image_image2_distrib <| smul_mul' _
  smul_one := fun _ =>
    image_singleton.trans <| by
      rw [smul_one, singleton_one]

localized [Pointwise] attribute [instance] Set.distribMulActionSet Set.mulDistribMulActionSet

instance [Zero α] [Zero β] [HasSmul α β] [NoZeroSmulDivisors α β] : NoZeroSmulDivisors (Set α) (Set β) :=
  ⟨fun s t h => by
    by_contra' H
    have hst : (s • t).Nonempty := h.symm.subst zero_nonempty
    simp_rw [← hst.of_smul_left.subset_zero_iff, ← hst.of_smul_right.subset_zero_iff, not_subset, mem_zero] at H
    obtain ⟨⟨a, hs, ha⟩, b, ht, hb⟩ := H
    exact (eq_zero_or_eq_zero_of_smul_eq_zero <| h.subset <| smul_mem_smul hs ht).elim ha hb⟩

instance no_zero_smul_divisors_set [Zero α] [Zero β] [HasSmul α β] [NoZeroSmulDivisors α β] :
    NoZeroSmulDivisors α (Set β) :=
  ⟨fun a s h => by
    by_contra' H
    have hst : (a • s).Nonempty := h.symm.subst zero_nonempty
    simp_rw [← hst.of_image.subset_zero_iff, not_subset, mem_zero] at H
    obtain ⟨ha, b, ht, hb⟩ := H
    exact (eq_zero_or_eq_zero_of_smul_eq_zero <| h.subset <| smul_mem_smul_set ht).elim ha hb⟩

instance [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (Set α) :=
  ⟨fun s t h => eq_zero_or_eq_zero_of_smul_eq_zero h⟩

end Smul

section Vsub

variable {ι : Sort _} {κ : ι → Sort _} [HasVsub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α} {b c : β}

include α

instance hasVsub : HasVsub (Set α) (Set β) :=
  ⟨Image2 (· -ᵥ ·)⟩

@[simp]
theorem image2_vsub : (Image2 HasVsub.vsub s t : Set α) = s -ᵥ t :=
  rfl

theorem image_vsub_prod : (fun x : β × β => x.fst -ᵥ x.snd) '' s ×ˢ t = s -ᵥ t :=
  image_prod _

theorem mem_vsub : a ∈ s -ᵥ t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x -ᵥ y = a :=
  Iff.rfl

theorem vsub_mem_vsub (hb : b ∈ s) (hc : c ∈ t) : b -ᵥ c ∈ s -ᵥ t :=
  mem_image2_of_mem hb hc

@[simp]
theorem empty_vsub (t : Set β) : ∅ -ᵥ t = ∅ :=
  image2_empty_left

@[simp]
theorem vsub_empty (s : Set β) : s -ᵥ ∅ = ∅ :=
  image2_empty_right

@[simp]
theorem vsub_eq_empty : s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff

@[simp]
theorem vsub_nonempty : (s -ᵥ t : Set α).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff

theorem Nonempty.vsub : s.Nonempty → t.Nonempty → (s -ᵥ t : Set α).Nonempty :=
  nonempty.image2

theorem Nonempty.of_vsub_left : (s -ᵥ t : Set α).Nonempty → s.Nonempty :=
  nonempty.of_image2_left

theorem Nonempty.of_vsub_right : (s -ᵥ t : Set α).Nonempty → t.Nonempty :=
  nonempty.of_image2_right

@[simp]
theorem vsub_singleton (s : Set β) (b : β) : s -ᵥ {b} = (· -ᵥ b) '' s :=
  image2_singleton_right

@[simp]
theorem singleton_vsub (t : Set β) (b : β) : {b} -ᵥ t = (· -ᵥ ·) b '' t :=
  image2_singleton_left

@[simp]
theorem singleton_vsub_singleton : ({b} : Set β) -ᵥ {c} = {b -ᵥ c} :=
  image2_singleton

@[mono]
theorem vsub_subset_vsub : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ :=
  image2_subset

theorem vsub_subset_vsub_left : t₁ ⊆ t₂ → s -ᵥ t₁ ⊆ s -ᵥ t₂ :=
  image2_subset_left

theorem vsub_subset_vsub_right : s₁ ⊆ s₂ → s₁ -ᵥ t ⊆ s₂ -ᵥ t :=
  image2_subset_right

theorem vsub_subset_iff : s -ᵥ t ⊆ u ↔ ∀, ∀ x ∈ s, ∀, ∀ y ∈ t, ∀, x -ᵥ y ∈ u :=
  image2_subset_iff

theorem vsub_self_mono (h : s ⊆ t) : s -ᵥ s ⊆ t -ᵥ t :=
  vsub_subset_vsub h h

theorem union_vsub : s₁ ∪ s₂ -ᵥ t = s₁ -ᵥ t ∪ (s₂ -ᵥ t) :=
  image2_union_left

theorem vsub_union : s -ᵥ (t₁ ∪ t₂) = s -ᵥ t₁ ∪ (s -ᵥ t₂) :=
  image2_union_right

theorem inter_vsub_subset : s₁ ∩ s₂ -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) :=
  image2_inter_subset_left

theorem vsub_inter_subset : s -ᵥ t₁ ∩ t₂ ⊆ (s -ᵥ t₁) ∩ (s -ᵥ t₂) :=
  image2_inter_subset_right

theorem Union_vsub_left_image : (⋃ a ∈ s, (· -ᵥ ·) a '' t) = s -ᵥ t :=
  Union_image_left _

theorem Union_vsub_right_image : (⋃ a ∈ t, (· -ᵥ a) '' s) = s -ᵥ t :=
  Union_image_right _

theorem Union_vsub (s : ι → Set β) (t : Set β) : (⋃ i, s i) -ᵥ t = ⋃ i, s i -ᵥ t :=
  image2_Union_left _ _ _

theorem vsub_Union (s : Set β) (t : ι → Set β) : (s -ᵥ ⋃ i, t i) = ⋃ i, s -ᵥ t i :=
  image2_Union_right _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem Union₂_vsub (s : ∀ i, κ i → Set β) (t : Set β) : (⋃ (i) (j), s i j) -ᵥ t = ⋃ (i) (j), s i j -ᵥ t :=
  image2_Union₂_left _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem vsub_Union₂ (s : Set β) (t : ∀ i, κ i → Set β) : (s -ᵥ ⋃ (i) (j), t i j) = ⋃ (i) (j), s -ᵥ t i j :=
  image2_Union₂_right _ _ _

theorem Inter_vsub_subset (s : ι → Set β) (t : Set β) : (⋂ i, s i) -ᵥ t ⊆ ⋂ i, s i -ᵥ t :=
  image2_Inter_subset_left _ _ _

theorem vsub_Inter_subset (s : Set β) (t : ι → Set β) : (s -ᵥ ⋂ i, t i) ⊆ ⋂ i, s -ᵥ t i :=
  image2_Inter_subset_right _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem Inter₂_vsub_subset (s : ∀ i, κ i → Set β) (t : Set β) : (⋂ (i) (j), s i j) -ᵥ t ⊆ ⋂ (i) (j), s i j -ᵥ t :=
  image2_Inter₂_subset_left _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem vsub_Inter₂_subset (s : Set β) (t : ∀ i, κ i → Set β) : (s -ᵥ ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s -ᵥ t i j :=
  image2_Inter₂_subset_right _ _ _

theorem Finite.vsub (hs : s.Finite) (ht : t.Finite) : Set.Finite (s -ᵥ t) :=
  hs.Image2 _ ht

end Vsub

open Pointwise

section Ringₓ

variable [Ringₓ α] [AddCommGroupₓ β] [Module α β] {s : Set α} {t : Set β} {a : α}

@[simp]
theorem neg_smul_set : -a • t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg, image_image, neg_smul]

@[simp]
theorem smul_set_neg : a • -t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg, image_image, smul_neg]

@[simp]
protected theorem neg_smul : -s • t = -(s • t) := by
  simp_rw [← image_neg]
  exact image2_image_left_comm neg_smul

@[simp]
protected theorem smul_neg : s • -t = -(s • t) := by
  simp_rw [← image_neg]
  exact image_image2_right_comm smul_neg

end Ringₓ

section SmulWithZero

variable [Zero α] [Zero β] [SmulWithZero α β] {s : Set α} {t : Set β}

/-!
Note that we have neither `smul_with_zero α (set β)` nor `smul_with_zero (set α) (set β)`
because `0 * ∅ ≠ 0`.
-/


theorem smul_zero_subset (s : Set α) : s • (0 : Set β) ⊆ 0 := by
  simp [← subset_def, ← mem_smul]

theorem zero_smul_subset (t : Set β) : (0 : Set α) • t ⊆ 0 := by
  simp [← subset_def, ← mem_smul]

theorem Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Set β) = 0 :=
  s.smul_zero_subset.antisymm <| by
    simpa [← mem_smul] using hs

theorem Nonempty.zero_smul (ht : t.Nonempty) : (0 : Set α) • t = 0 :=
  t.zero_smul_subset.antisymm <| by
    simpa [← mem_smul] using ht

/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
theorem zero_smul_set {s : Set β} (h : s.Nonempty) : (0 : α) • s = (0 : Set β) := by
  simp only [image_smul, ← image_eta, ← zero_smul, ← h.image_const, ← singleton_zero]

theorem zero_smul_set_subset (s : Set β) : (0 : α) • s ⊆ 0 :=
  image_subset_iff.2 fun x _ => zero_smul α x

theorem subsingleton_zero_smul_set (s : Set β) : ((0 : α) • s).Subsingleton :=
  subsingleton_singleton.mono <| zero_smul_set_subset s

theorem zero_mem_smul_set {t : Set β} {a : α} (h : (0 : β) ∈ t) : (0 : β) ∈ a • t :=
  ⟨0, h, smul_zero' _ _⟩

variable [NoZeroSmulDivisors α β] {a : α}

theorem zero_mem_smul_iff : (0 : β) ∈ s • t ↔ (0 : α) ∈ s ∧ t.Nonempty ∨ (0 : β) ∈ t ∧ s.Nonempty := by
  constructor
  · rintro ⟨a, b, ha, hb, h⟩
    obtain rfl | rfl := eq_zero_or_eq_zero_of_smul_eq_zero h
    · exact Or.inl ⟨ha, b, hb⟩
      
    · exact Or.inr ⟨hb, a, ha⟩
      
    
  · rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩)
    · exact ⟨0, b, hs, hb, zero_smul _ _⟩
      
    · exact ⟨a, 0, ha, ht, smul_zero' _ _⟩
      
    

theorem zero_mem_smul_set_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t := by
  refine' ⟨_, zero_mem_smul_set⟩
  rintro ⟨b, hb, h⟩
  rwa [(eq_zero_or_eq_zero_of_smul_eq_zero h).resolve_left ha] at hb

end SmulWithZero

section LeftCancelSemigroup

variable [LeftCancelSemigroup α] {s t : Set α}

@[to_additive]
theorem pairwise_disjoint_smul_iff : s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t : Set (α × α)).InjOn fun p => p.1 * p.2 :=
  pairwise_disjoint_image_right_iff fun _ _ => mul_right_injective _

end LeftCancelSemigroup

section Groupₓ

variable [Groupₓ α] [MulAction α β] {s t A B : Set β} {a : α} {x : β}

@[simp, to_additive]
theorem smul_mem_smul_set_iff : a • x ∈ a • s ↔ x ∈ s :=
  (MulAction.injective _).mem_set_image

@[to_additive]
theorem mem_smul_set_iff_inv_smul_mem : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show x ∈ MulAction.toPerm a '' A ↔ _ from mem_image_equiv

@[to_additive]
theorem mem_inv_smul_set_iff : x ∈ a⁻¹ • A ↔ a • x ∈ A := by
  simp only [image_smul, ← mem_image, ← inv_smul_eq_iff, ← exists_eq_right]

@[to_additive]
theorem preimage_smul (a : α) (t : Set β) : (fun x => a • x) ⁻¹' t = a⁻¹ • t :=
  ((MulAction.toPerm a).symm.image_eq_preimage _).symm

@[to_additive]
theorem preimage_smul_inv (a : α) (t : Set β) : (fun x => a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (toUnits a)⁻¹ t

@[simp, to_additive]
theorem set_smul_subset_set_smul_iff : a • A ⊆ a • B ↔ A ⊆ B :=
  image_subset_image_iff <| MulAction.injective _

@[to_additive]
theorem set_smul_subset_iff : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  image_subset_iff.trans <| iff_of_eq <| congr_arg _ <| preimage_equiv_eq_image_symm _ <| MulAction.toPerm _

@[to_additive]
theorem subset_set_smul_iff : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  Iff.symm <|
    image_subset_iff.trans <|
      Iff.symm <| iff_of_eq <| congr_arg _ <| image_equiv_eq_preimage_symm _ <| MulAction.toPerm _

end Groupₓ

section GroupWithZeroₓ

variable [GroupWithZeroₓ α] [MulAction α β] {s : Set α} {a : α}

@[simp]
theorem smul_mem_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : a • x ∈ a • A ↔ x ∈ A :=
  show Units.mk0 a ha • _ ∈ _ ↔ _ from smul_mem_smul_set_iff

theorem mem_smul_set_iff_inv_smul_mem₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show _ ∈ Units.mk0 a ha • _ ↔ _ from mem_smul_set_iff_inv_smul_mem

theorem mem_inv_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
  show _ ∈ (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_set_iff

theorem preimage_smul₀ (ha : a ≠ 0) (t : Set β) : (fun x => a • x) ⁻¹' t = a⁻¹ • t :=
  preimage_smul (Units.mk0 a ha) t

theorem preimage_smul_inv₀ (ha : a ≠ 0) (t : Set β) : (fun x => a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (Units.mk0 a ha)⁻¹ t

@[simp]
theorem set_smul_subset_set_smul_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ a • B ↔ A ⊆ B :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from set_smul_subset_set_smul_iff

theorem set_smul_subset_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from set_smul_subset_iff

theorem subset_set_smul_iff₀ (ha : a ≠ 0) {A B : Set β} : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  show _ ⊆ Units.mk0 a ha • _ ↔ _ from subset_set_smul_iff

theorem smul_univ₀ (hs : ¬s ⊆ 0) : s • (Univ : Set β) = univ :=
  let ⟨a, ha, ha₀⟩ := not_subset.1 hs
  eq_univ_of_forall fun b => ⟨a, a⁻¹ • b, ha, trivialₓ, smul_inv_smul₀ ha₀ _⟩

theorem smul_set_univ₀ (ha : a ≠ 0) : a • (Univ : Set β) = univ :=
  eq_univ_of_forall fun b => ⟨a⁻¹ • b, trivialₓ, smul_inv_smul₀ ha _⟩

end GroupWithZeroₓ

end Set

/-! ### Miscellaneous -/


open Set

open Pointwise

/-! Some lemmas about pointwise multiplication and submonoids. Ideally we put these in
  `group_theory.submonoid.basic`, but currently we cannot because that file is imported by this. -/


namespace Submonoid

variable {M : Type _} [Monoidₓ M] {s t u : Set M}

@[to_additive]
theorem mul_subset {S : Submonoid M} (hs : s ⊆ S) (ht : t ⊆ S) : s * t ⊆ S := by
  rintro _ ⟨p, q, hp, hq, rfl⟩
  exact Submonoid.mul_mem _ (hs hp) (ht hq)

@[to_additive]
theorem mul_subset_closure (hs : s ⊆ u) (ht : t ⊆ u) : s * t ⊆ Submonoid.closure u :=
  mul_subset (Subset.trans hs Submonoid.subset_closure) (Subset.trans ht Submonoid.subset_closure)

@[to_additive]
theorem coe_mul_self_eq (s : Submonoid M) : (s : Set M) * s = s := by
  ext x
  refine' ⟨_, fun h => ⟨x, 1, h, s.one_mem, mul_oneₓ x⟩⟩
  rintro ⟨a, b, ha, hb, rfl⟩
  exact s.mul_mem ha hb

@[to_additive]
theorem closure_mul_le (S T : Set M) : closure (S * T) ≤ closure S⊔closure T :=
  Inf_le fun x ⟨s, t, hs, ht, hx⟩ =>
    hx ▸
      (closure S⊔closure T).mul_mem (SetLike.le_def.mp le_sup_left <| subset_closure hs)
        (SetLike.le_def.mp le_sup_right <| subset_closure ht)

@[to_additive]
theorem sup_eq_closure (H K : Submonoid M) : H⊔K = closure (H * K) :=
  le_antisymmₓ
    (sup_le (fun h hh => subset_closure ⟨h, 1, hh, K.one_mem, mul_oneₓ h⟩) fun k hk =>
      subset_closure ⟨1, k, H.one_mem, hk, one_mulₓ k⟩)
    (by
      conv_rhs => rw [← closure_eq H, ← closure_eq K] <;> apply closure_mul_le)

theorem pow_smul_mem_closure_smul {N : Type _} [CommMonoidₓ N] [MulAction M N] [IsScalarTower M N N] (r : M) (s : Set N)
    {x : N} (hx : x ∈ closure s) : ∃ n : ℕ, r ^ n • x ∈ closure (r • s) := by
  apply @closure_induction N _ s (fun x : N => ∃ n : ℕ, r ^ n • x ∈ closure (r • s)) _ hx
  · intro x hx
    exact
      ⟨1,
        subset_closure
          ⟨_, hx, by
            rw [pow_oneₓ]⟩⟩
    
  · exact
      ⟨0, by
        simpa using one_mem _⟩
    
  · rintro x y ⟨nx, hx⟩ ⟨ny, hy⟩
    use nx + ny
    convert mul_mem hx hy
    rw [pow_addₓ, smul_mul_assoc, mul_smul, mul_comm, ← smul_mul_assoc, mul_comm]
    

end Submonoid

namespace Groupₓ

theorem card_pow_eq_card_pow_card_univ_aux {f : ℕ → ℕ} (h1 : Monotone f) {B : ℕ} (h2 : ∀ n, f n ≤ B)
    (h3 : ∀ n, f n = f (n + 1) → f (n + 1) = f (n + 2)) : ∀ k, B ≤ k → f k = f B := by
  have key : ∃ n : ℕ, n ≤ B ∧ f n = f (n + 1) := by
    contrapose! h2
    suffices ∀ n : ℕ, n ≤ B + 1 → n ≤ f n by
      exact ⟨B + 1, this (B + 1) (le_reflₓ (B + 1))⟩
    exact fun n =>
      Nat.rec (fun h => Nat.zero_leₓ (f 0))
        (fun n ih h =>
          lt_of_le_of_ltₓ (ih (n.le_succ.trans h)) (lt_of_le_of_neₓ (h1 n.le_succ) (h2 n (nat.succ_le_succ_iff.mp h))))
        n
  · obtain ⟨n, hn1, hn2⟩ := key
    replace key : ∀ k : ℕ, f (n + k) = f (n + k + 1) ∧ f (n + k) = f n := fun k =>
      Nat.rec ⟨hn2, rfl⟩ (fun k ih => ⟨h3 _ ih.1, ih.1.symm.trans ih.2⟩) k
    replace key : ∀ k : ℕ, n ≤ k → f k = f n := fun k hk =>
      (congr_arg f (add_tsub_cancel_of_le hk)).symm.trans (key (k - n)).2
    exact fun k hk => (key k (hn1.trans hk)).trans (key B hn1).symm
    

variable {G : Type _} [Groupₓ G] [Fintype G] (S : Set G)

-- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Interactive.lean:71:16: TODO classical! not yet supported
@[to_additive]
theorem card_pow_eq_card_pow_card_univ [∀ k : ℕ, DecidablePred (· ∈ S ^ k)] :
    ∀ k, Fintype.card G ≤ k → Fintype.card ↥(S ^ k) = Fintype.card ↥(S ^ Fintype.card G) := by
  have hG : 0 < Fintype.card G := fintype.card_pos_iff.mpr ⟨1⟩
  by_cases' hS : S = ∅
  · refine' fun k hk => Fintype.card_congr _
    rw [hS, empty_pow (ne_of_gtₓ (lt_of_lt_of_leₓ hG hk)), empty_pow (ne_of_gtₓ hG)]
    
  obtain ⟨a, ha⟩ := set.ne_empty_iff_nonempty.mp hS
  classical
  have key : ∀ (a) (s t : Set G), (∀ b : G, b ∈ s → a * b ∈ t) → Fintype.card s ≤ Fintype.card t := by
    refine' fun a s t h => Fintype.card_le_of_injective (fun ⟨b, hb⟩ => ⟨a * b, h b hb⟩) _
    rintro ⟨b, hb⟩ ⟨c, hc⟩ hbc
    exact Subtype.ext (mul_left_cancelₓ (subtype.ext_iff.mp hbc))
  have mono : Monotone (fun n => Fintype.card ↥(S ^ n) : ℕ → ℕ) :=
    monotone_nat_of_le_succ fun n => key a _ _ fun b hb => Set.mul_mem_mul ha hb
  convert
    card_pow_eq_card_pow_card_univ_aux mono (fun n => set_fintype_card_le_univ (S ^ n)) fun n h =>
      le_antisymmₓ (mono (n + 1).le_succ) (key a⁻¹ _ _ _)
  · simp only [← Finset.filter_congr_decidable, ← Fintype.card_of_finset]
    
  replace h : {a} * S ^ n = S ^ (n + 1)
  · refine' Set.eq_of_subset_of_card_le _ (le_transₓ (ge_of_eq h) _)
    · exact mul_subset_mul (set.singleton_subset_iff.mpr ha) Set.Subset.rfl
      
    · convert key a (S ^ n) ({a} * S ^ n) fun b hb => Set.mul_mem_mul (Set.mem_singleton a) hb
      
    
  rw [pow_succ'ₓ, ← h, mul_assoc, ← pow_succ'ₓ, h]
  rintro _ ⟨b, c, hb, hc, rfl⟩
  rwa [set.mem_singleton_iff.mp hb, inv_mul_cancel_leftₓ]

end Groupₓ

