/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.Algebra.Order.Monoid

/-!
# Ordered Subtraction

This file proves lemmas relating (truncated) subtraction with an order. We provide a class
`has_ordered_sub` stating that `a - b ≤ c ↔ a ≤ c + b`.

The subtraction discussed here could both be normal subtraction in an additive group or truncated
subtraction on a canonically ordered monoid (`ℕ`, `multiset`, `part_enat`, `ennreal`, ...)

## Implementation details

`has_ordered_sub` is a mixin type-class, so that we can use the results in this file even in cases
where we don't have a `canonically_ordered_add_monoid` instance
(even though that is our main focus). Conversely, this means we can use
`canonically_ordered_add_monoid` without necessarily having to define a subtraction.

The results in this file are ordered by the type-class assumption needed to prove it.
This means that similar results might not be close to each other. Furthermore, we don't prove
implications if a bi-implication can be proven under the same assumptions.

Lemmas using this class are named using `tsub` instead of `sub` (short for "truncated subtraction").
This is to avoid naming conflicts with similar lemmas about ordered groups.

We provide a second version of most results that require `[contravariant_class α α (+) (≤)]`. In the
second version we replace this type-class assumption by explicit `add_le_cancellable` assumptions.

TODO: maybe we should make a multiplicative version of this, so that we can replace some identical
lemmas about subtraction/division in `ordered_[add_]comm_group` with these.

TODO: generalize `nat.le_of_le_of_sub_le_sub_right`, `nat.sub_le_sub_right_iff`,
  `nat.mul_self_sub_mul_self_eq`
-/


variable {α β : Type _}

/-- `has_ordered_sub α` means that `α` has a subtraction characterized by `a - b ≤ c ↔ a ≤ c + b`.
In other words, `a - b` is the least `c` such that `a ≤ b + c`.

This is satisfied both by the subtraction in additive ordered groups and by truncated subtraction
in canonically ordered monoids on many specific types.
-/
class HasOrderedSub (α : Type _) [LE α] [Add α] [Sub α] where
  tsub_le_iff_right : ∀ a b c : α, a - b ≤ c ↔ a ≤ c + b

section Add

variable [Preorderₓ α] [Add α] [Sub α] [HasOrderedSub α] {a b c d : α}

@[simp]
theorem tsub_le_iff_right : a - b ≤ c ↔ a ≤ c + b :=
  HasOrderedSub.tsub_le_iff_right a b c

/-- See `add_tsub_cancel_right` for the equality if `contravariant_class α α (+) (≤)`. -/
theorem add_tsub_le_right : a + b - b ≤ a :=
  tsub_le_iff_right.mpr le_rfl

theorem le_tsub_add : b ≤ b - a + a :=
  tsub_le_iff_right.mp le_rfl

theorem AddHom.le_map_tsub [Preorderₓ β] [Add β] [Sub β] [HasOrderedSub β] (f : AddHom α β) (hf : Monotone f)
    (a b : α) : f a - f b ≤ f (a - b) := by
  rw [tsub_le_iff_right, ← f.map_add]
  exact hf le_tsub_add

theorem le_mul_tsub {R : Type _} [Distribₓ R] [Preorderₓ R] [Sub R] [HasOrderedSub R]
    [CovariantClass R R (· * ·) (· ≤ ·)] {a b c : R} : a * b - a * c ≤ a * (b - c) :=
  (AddHom.mulLeft a).le_map_tsub (monotone_id.const_mul' a) _ _

theorem le_tsub_mul {R : Type _} [CommSemiringₓ R] [Preorderₓ R] [Sub R] [HasOrderedSub R]
    [CovariantClass R R (· * ·) (· ≤ ·)] {a b c : R} : a * c - b * c ≤ (a - b) * c := by
  simpa only [← mul_comm _ c] using le_mul_tsub

end Add

/-- An order isomorphism between types with ordered subtraction preserves subtraction provided that
it preserves addition. -/
theorem OrderIso.map_tsub {M N : Type _} [Preorderₓ M] [Add M] [Sub M] [HasOrderedSub M] [PartialOrderₓ N] [Add N]
    [Sub N] [HasOrderedSub N] (e : M ≃o N) (h_add : ∀ a b, e (a + b) = e a + e b) (a b : M) : e (a - b) = e a - e b :=
  by
  set e_add : M ≃+ N := { e with map_add' := h_add }
  refine' le_antisymmₓ _ (e_add.to_add_hom.le_map_tsub e.monotone a b)
  suffices e (e.symm (e a) - e.symm (e b)) ≤ e (e.symm (e a - e b)) by
    simpa
  exact e.monotone (e_add.symm.to_add_hom.le_map_tsub e.symm.monotone _ _)

/-! ### Preorder -/


section OrderedAddCommMonoid

section Preorderₓ

variable [Preorderₓ α]

section AddCommSemigroupₓ

variable [AddCommSemigroupₓ α] [Sub α] [HasOrderedSub α] {a b c d : α}

theorem tsub_le_iff_left : a - b ≤ c ↔ a ≤ b + c := by
  rw [tsub_le_iff_right, add_commₓ]

theorem le_add_tsub : a ≤ b + (a - b) :=
  tsub_le_iff_left.mp le_rfl

/-- See `add_tsub_cancel_left` for the equality if `contravariant_class α α (+) (≤)`. -/
theorem add_tsub_le_left : a + b - a ≤ b :=
  tsub_le_iff_left.mpr le_rfl

theorem tsub_le_tsub_right (h : a ≤ b) (c : α) : a - c ≤ b - c :=
  tsub_le_iff_left.mpr <| h.trans le_add_tsub

theorem tsub_le_iff_tsub_le : a - b ≤ c ↔ a - c ≤ b := by
  rw [tsub_le_iff_left, tsub_le_iff_right]

/-- See `tsub_tsub_cancel_of_le` for the equality. -/
theorem tsub_tsub_le : b - (b - a) ≤ a :=
  tsub_le_iff_right.mpr le_add_tsub

section Cov

variable [CovariantClass α α (· + ·) (· ≤ ·)]

theorem tsub_le_tsub_left (h : a ≤ b) (c : α) : c - b ≤ c - a :=
  tsub_le_iff_left.mpr <| le_add_tsub.trans <| add_le_add_right h _

theorem tsub_le_tsub (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
  (tsub_le_tsub_right hab _).trans <| tsub_le_tsub_left hcd _

/-- See `add_tsub_assoc_of_le` for the equality. -/
theorem add_tsub_le_assoc : a + b - c ≤ a + (b - c) := by
  rw [tsub_le_iff_left, add_left_commₓ]
  exact add_le_add_left le_add_tsub a

theorem add_le_add_add_tsub : a + b ≤ a + c + (b - c) := by
  rw [add_assocₓ]
  exact add_le_add_left le_add_tsub a

theorem le_tsub_add_add : a + b ≤ a - c + (b + c) := by
  rw [add_commₓ a, add_commₓ (a - c)]
  exact add_le_add_add_tsub

theorem tsub_le_tsub_add_tsub : a - c ≤ a - b + (b - c) := by
  rw [tsub_le_iff_left, ← add_assocₓ, add_right_commₓ]
  exact le_add_tsub.trans (add_le_add_right le_add_tsub _)

theorem tsub_tsub_tsub_le_tsub : c - a - (c - b) ≤ b - a := by
  rw [tsub_le_iff_left, tsub_le_iff_left, add_left_commₓ]
  exact le_tsub_add.trans (add_le_add_left le_add_tsub _)

theorem tsub_tsub_le_tsub_add {a b c : α} : a - (b - c) ≤ a - b + c :=
  tsub_le_iff_right.2 <|
    calc
      a ≤ a - b + b := le_tsub_add
      _ ≤ a - b + (c + (b - c)) := add_le_add_left le_add_tsub _
      _ = a - b + c + (b - c) := (add_assocₓ _ _ _).symm
      

end Cov

/-! #### Lemmas that assume that an element is `add_le_cancellable` -/


namespace AddLeCancellable

protected theorem le_add_tsub_swap (hb : AddLeCancellable b) : a ≤ b + a - b :=
  hb le_add_tsub

protected theorem le_add_tsub (hb : AddLeCancellable b) : a ≤ a + b - b := by
  rw [add_commₓ]
  exact hb.le_add_tsub_swap

protected theorem le_tsub_of_add_le_left (ha : AddLeCancellable a) (h : a + b ≤ c) : b ≤ c - a :=
  ha <| h.trans le_add_tsub

protected theorem le_tsub_of_add_le_right (hb : AddLeCancellable b) (h : a + b ≤ c) : a ≤ c - b :=
  hb.le_tsub_of_add_le_left <| by
    rwa [add_commₓ]

end AddLeCancellable

/-! ### Lemmas where addition is order-reflecting -/


section Contra

variable [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem le_add_tsub_swap : a ≤ b + a - b :=
  Contravariant.add_le_cancellable.le_add_tsub_swap

theorem le_add_tsub' : a ≤ a + b - b :=
  Contravariant.add_le_cancellable.le_add_tsub

theorem le_tsub_of_add_le_left (h : a + b ≤ c) : b ≤ c - a :=
  Contravariant.add_le_cancellable.le_tsub_of_add_le_left h

theorem le_tsub_of_add_le_right (h : a + b ≤ c) : a ≤ c - b :=
  Contravariant.add_le_cancellable.le_tsub_of_add_le_right h

end Contra

end AddCommSemigroupₓ

variable [AddCommMonoidₓ α] [Sub α] [HasOrderedSub α] {a b c d : α}

theorem tsub_nonpos : a - b ≤ 0 ↔ a ≤ b := by
  rw [tsub_le_iff_left, add_zeroₓ]

alias tsub_nonpos ↔ _ tsub_nonpos_of_le

theorem AddMonoidHom.le_map_tsub [Preorderₓ β] [AddCommMonoidₓ β] [Sub β] [HasOrderedSub β] (f : α →+ β)
    (hf : Monotone f) (a b : α) : f a - f b ≤ f (a - b) :=
  f.toAddHom.le_map_tsub hf a b

end Preorderₓ

/-! ### Partial order -/


variable [PartialOrderₓ α] [AddCommSemigroupₓ α] [Sub α] [HasOrderedSub α] {a b c d : α}

theorem tsub_tsub (b a c : α) : b - a - c = b - (a + c) := by
  apply le_antisymmₓ
  · rw [tsub_le_iff_left, tsub_le_iff_left, ← add_assocₓ, ← tsub_le_iff_left]
    
  · rw [tsub_le_iff_left, add_assocₓ, ← tsub_le_iff_left, ← tsub_le_iff_left]
    

section Cov

variable [CovariantClass α α (· + ·) (· ≤ ·)]

theorem tsub_add_eq_tsub_tsub (a b c : α) : a - (b + c) = a - b - c := by
  refine' le_antisymmₓ (tsub_le_iff_left.mpr _) (tsub_le_iff_left.mpr <| tsub_le_iff_left.mpr _)
  · rw [add_assocₓ]
    refine' le_transₓ le_add_tsub (add_le_add_left le_add_tsub _)
    
  · rw [← add_assocₓ]
    apply le_add_tsub
    

theorem tsub_add_eq_tsub_tsub_swap (a b c : α) : a - (b + c) = a - c - b := by
  rw [add_commₓ]
  apply tsub_add_eq_tsub_tsub

theorem tsub_right_comm : a - b - c = a - c - b := by
  simp_rw [← tsub_add_eq_tsub_tsub, add_commₓ]

theorem add_tsub_add_le_tsub_add_tsub : a + b - (c + d) ≤ a - c + (b - d) := by
  rw [add_commₓ c, ← tsub_tsub]
  refine' (tsub_le_tsub_right add_tsub_le_assoc c).trans _
  rw [add_commₓ a, add_commₓ (a - c)]
  exact add_tsub_le_assoc

end Cov

/-! ### Lemmas that assume that an element is `add_le_cancellable`. -/


namespace AddLeCancellable

protected theorem tsub_eq_of_eq_add (hb : AddLeCancellable b) (h : a = c + b) : a - b = c :=
  le_antisymmₓ (tsub_le_iff_right.mpr h.le) <| by
    rw [h]
    exact hb.le_add_tsub

protected theorem eq_tsub_of_add_eq (hc : AddLeCancellable c) (h : a + c = b) : a = b - c :=
  (hc.tsub_eq_of_eq_add h.symm).symm

protected theorem tsub_eq_of_eq_add_rev (hb : AddLeCancellable b) (h : a = b + c) : a - b = c :=
  hb.tsub_eq_of_eq_add <| by
    rw [add_commₓ, h]

@[simp]
protected theorem add_tsub_cancel_right (hb : AddLeCancellable b) : a + b - b = a :=
  hb.tsub_eq_of_eq_add <| by
    rw [add_commₓ]

@[simp]
protected theorem add_tsub_cancel_left (ha : AddLeCancellable a) : a + b - a = b :=
  ha.tsub_eq_of_eq_add <| add_commₓ a b

protected theorem lt_add_of_tsub_lt_left (hb : AddLeCancellable b) (h : a - b < c) : a < b + c := by
  rw [lt_iff_le_and_ne, ← tsub_le_iff_left]
  refine' ⟨h.le, _⟩
  rintro rfl
  simpa [← hb] using h

protected theorem lt_add_of_tsub_lt_right (hc : AddLeCancellable c) (h : a - c < b) : a < b + c := by
  rw [lt_iff_le_and_ne, ← tsub_le_iff_right]
  refine' ⟨h.le, _⟩
  rintro rfl
  simpa [← hc] using h

end AddLeCancellable

/-! #### Lemmas where addition is order-reflecting. -/


section Contra

variable [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem tsub_eq_of_eq_add (h : a = c + b) : a - b = c :=
  Contravariant.add_le_cancellable.tsub_eq_of_eq_add h

theorem eq_tsub_of_add_eq (h : a + c = b) : a = b - c :=
  Contravariant.add_le_cancellable.eq_tsub_of_add_eq h

theorem tsub_eq_of_eq_add_rev (h : a = b + c) : a - b = c :=
  Contravariant.add_le_cancellable.tsub_eq_of_eq_add_rev h

@[simp]
theorem add_tsub_cancel_right (a b : α) : a + b - b = a :=
  Contravariant.add_le_cancellable.add_tsub_cancel_right

@[simp]
theorem add_tsub_cancel_left (a b : α) : a + b - a = b :=
  Contravariant.add_le_cancellable.add_tsub_cancel_left

theorem lt_add_of_tsub_lt_left (h : a - b < c) : a < b + c :=
  Contravariant.add_le_cancellable.lt_add_of_tsub_lt_left h

theorem lt_add_of_tsub_lt_right (h : a - c < b) : a < b + c :=
  Contravariant.add_le_cancellable.lt_add_of_tsub_lt_right h

end Contra

section Both

variable [CovariantClass α α (· + ·) (· ≤ ·)] [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem add_tsub_add_eq_tsub_right (a c b : α) : a + c - (b + c) = a - b := by
  apply le_antisymmₓ
  · rw [tsub_le_iff_left, add_right_commₓ]
    exact add_le_add_right le_add_tsub c
    
  · rw [tsub_le_iff_left, add_commₓ b]
    apply le_of_add_le_add_right
    rw [add_assocₓ]
    exact le_tsub_add
    

theorem add_tsub_add_eq_tsub_left (a b c : α) : a + b - (a + c) = b - c := by
  rw [add_commₓ a b, add_commₓ a c, add_tsub_add_eq_tsub_right]

end Both

end OrderedAddCommMonoid

/-! ### Lemmas in a linearly ordered monoid. -/


section LinearOrderₓ

variable {a b c d : α} [LinearOrderₓ α] [AddCommSemigroupₓ α] [Sub α] [HasOrderedSub α]

/-- See `lt_of_tsub_lt_tsub_right_of_le` for a weaker statement in a partial order. -/
theorem lt_of_tsub_lt_tsub_right (h : a - c < b - c) : a < b :=
  lt_imp_lt_of_le_imp_le (fun h => tsub_le_tsub_right h c) h

/-- See `lt_tsub_iff_right_of_le` for a weaker statement in a partial order. -/
theorem lt_tsub_iff_right : a < b - c ↔ a + c < b :=
  lt_iff_lt_of_le_iff_le tsub_le_iff_right

/-- See `lt_tsub_iff_left_of_le` for a weaker statement in a partial order. -/
theorem lt_tsub_iff_left : a < b - c ↔ c + a < b :=
  lt_iff_lt_of_le_iff_le tsub_le_iff_left

theorem lt_tsub_comm : a < b - c ↔ c < b - a :=
  lt_tsub_iff_left.trans lt_tsub_iff_right.symm

section Cov

variable [CovariantClass α α (· + ·) (· ≤ ·)]

/-- See `lt_of_tsub_lt_tsub_left_of_le` for a weaker statement in a partial order. -/
theorem lt_of_tsub_lt_tsub_left (h : a - b < a - c) : c < b :=
  lt_imp_lt_of_le_imp_le (fun h => tsub_le_tsub_left h a) h

end Cov

end LinearOrderₓ

/-! ### Lemmas in a canonically ordered monoid. -/


section CanonicallyOrderedAddMonoid

variable [CanonicallyOrderedAddMonoid α] [Sub α] [HasOrderedSub α] {a b c d : α}

@[simp]
theorem add_tsub_cancel_of_le (h : a ≤ b) : a + (b - a) = b := by
  refine' le_antisymmₓ _ le_add_tsub
  obtain ⟨c, rfl⟩ := le_iff_exists_add.1 h
  exact add_le_add_left add_tsub_le_left a

theorem tsub_add_cancel_of_le (h : a ≤ b) : b - a + a = b := by
  rw [add_commₓ]
  exact add_tsub_cancel_of_le h

theorem add_tsub_cancel_iff_le : a + (b - a) = b ↔ a ≤ b :=
  ⟨fun h => le_iff_exists_add.mpr ⟨b - a, h.symm⟩, add_tsub_cancel_of_le⟩

theorem tsub_add_cancel_iff_le : b - a + a = b ↔ a ≤ b := by
  rw [add_commₓ]
  exact add_tsub_cancel_iff_le

theorem add_le_of_le_tsub_right_of_le (h : b ≤ c) (h2 : a ≤ c - b) : a + b ≤ c :=
  (add_le_add_right h2 b).trans_eq <| tsub_add_cancel_of_le h

theorem add_le_of_le_tsub_left_of_le (h : a ≤ c) (h2 : b ≤ c - a) : a + b ≤ c :=
  (add_le_add_left h2 a).trans_eq <| add_tsub_cancel_of_le h

theorem tsub_le_tsub_iff_right (h : c ≤ b) : a - c ≤ b - c ↔ a ≤ b := by
  rw [tsub_le_iff_right, tsub_add_cancel_of_le h]

theorem tsub_left_inj (h1 : c ≤ a) (h2 : c ≤ b) : a - c = b - c ↔ a = b := by
  simp_rw [le_antisymm_iffₓ, tsub_le_tsub_iff_right h1, tsub_le_tsub_iff_right h2]

/-- See `lt_of_tsub_lt_tsub_right` for a stronger statement in a linear order. -/
theorem lt_of_tsub_lt_tsub_right_of_le (h : c ≤ b) (h2 : a - c < b - c) : a < b := by
  refine' ((tsub_le_tsub_iff_right h).mp h2.le).lt_of_ne _
  rintro rfl
  exact h2.false

@[simp]
theorem tsub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b := by
  rw [← nonpos_iff_eq_zero, tsub_le_iff_left, add_zeroₓ]

/-- One direction of `tsub_eq_zero_iff_le`, as a `@[simp]`-lemma. -/
@[simp]
theorem tsub_eq_zero_of_le (h : a ≤ b) : a - b = 0 :=
  tsub_eq_zero_iff_le.mpr h

@[simp]
theorem tsub_self (a : α) : a - a = 0 :=
  tsub_eq_zero_iff_le.mpr le_rfl

@[simp]
theorem tsub_le_self : a - b ≤ a :=
  tsub_le_iff_left.mpr <| le_add_left le_rfl

@[simp]
theorem tsub_zero (a : α) : a - 0 = a :=
  le_antisymmₓ tsub_le_self <| le_add_tsub.trans_eq <| zero_addₓ _

@[simp]
theorem zero_tsub (a : α) : 0 - a = 0 :=
  tsub_eq_zero_iff_le.mpr <| zero_le a

theorem tsub_self_add (a b : α) : a - (a + b) = 0 := by
  rw [tsub_eq_zero_iff_le]
  apply self_le_add_right

theorem tsub_inj_left (h₁ : a ≤ b) (h₂ : a ≤ c) (h₃ : b - a = c - a) : b = c := by
  rw [← tsub_add_cancel_of_le h₁, ← tsub_add_cancel_of_le h₂, h₃]

theorem tsub_pos_iff_not_le : 0 < a - b ↔ ¬a ≤ b := by
  rw [pos_iff_ne_zero, Ne.def, tsub_eq_zero_iff_le]

theorem tsub_pos_of_lt (h : a < b) : 0 < b - a :=
  tsub_pos_iff_not_le.mpr h.not_le

theorem tsub_add_tsub_cancel (hab : b ≤ a) (hbc : c ≤ b) : a - b + (b - c) = a - c := by
  convert tsub_add_cancel_of_le (tsub_le_tsub_right hab c) using 2
  rw [tsub_tsub, add_tsub_cancel_of_le hbc]

theorem tsub_tsub_tsub_cancel_right (h : c ≤ b) : a - c - (b - c) = a - b := by
  rw [tsub_tsub, add_tsub_cancel_of_le h]

theorem tsub_lt_of_lt (h : a < b) : a - c < b :=
  lt_of_le_of_ltₓ tsub_le_self h

/-! ### Lemmas that assume that an element is `add_le_cancellable`. -/


namespace AddLeCancellable

protected theorem eq_tsub_iff_add_eq_of_le (hc : AddLeCancellable c) (h : c ≤ b) : a = b - c ↔ a + c = b := by
  constructor
  · rintro rfl
    exact tsub_add_cancel_of_le h
    
  · rintro rfl
    exact hc.add_tsub_cancel_right.symm
    

protected theorem tsub_eq_iff_eq_add_of_le (hb : AddLeCancellable b) (h : b ≤ a) : a - b = c ↔ a = c + b := by
  rw [eq_comm, hb.eq_tsub_iff_add_eq_of_le h, eq_comm]

protected theorem add_tsub_assoc_of_le (hc : AddLeCancellable c) (h : c ≤ b) (a : α) : a + b - c = a + (b - c) := by
  conv_lhs => rw [← add_tsub_cancel_of_le h, add_commₓ c, ← add_assocₓ, hc.add_tsub_cancel_right]

protected theorem tsub_add_eq_add_tsub (hb : AddLeCancellable b) (h : b ≤ a) : a - b + c = a + c - b := by
  rw [add_commₓ a, hb.add_tsub_assoc_of_le h, add_commₓ]

protected theorem tsub_tsub_assoc (hbc : AddLeCancellable (b - c)) (h₁ : b ≤ a) (h₂ : c ≤ b) :
    a - (b - c) = a - b + c := by
  rw [hbc.tsub_eq_iff_eq_add_of_le (tsub_le_self.trans h₁), add_assocₓ, add_tsub_cancel_of_le h₂,
    tsub_add_cancel_of_le h₁]

protected theorem tsub_add_tsub_comm (hb : AddLeCancellable b) (hd : AddLeCancellable d) (hba : b ≤ a) (hdc : d ≤ c) :
    a - b + (c - d) = a + c - (b + d) := by
  rw [hb.tsub_add_eq_add_tsub hba, ← hd.add_tsub_assoc_of_le hdc, tsub_tsub, add_commₓ d]

protected theorem le_tsub_iff_left (ha : AddLeCancellable a) (h : a ≤ c) : b ≤ c - a ↔ a + b ≤ c :=
  ⟨add_le_of_le_tsub_left_of_le h, ha.le_tsub_of_add_le_left⟩

protected theorem le_tsub_iff_right (ha : AddLeCancellable a) (h : a ≤ c) : b ≤ c - a ↔ b + a ≤ c := by
  rw [add_commₓ]
  exact ha.le_tsub_iff_left h

protected theorem tsub_lt_iff_left (hb : AddLeCancellable b) (hba : b ≤ a) : a - b < c ↔ a < b + c := by
  refine' ⟨hb.lt_add_of_tsub_lt_left, _⟩
  intro h
  refine' (tsub_le_iff_left.mpr h.le).lt_of_ne _
  rintro rfl
  exact h.ne' (add_tsub_cancel_of_le hba)

protected theorem tsub_lt_iff_right (hb : AddLeCancellable b) (hba : b ≤ a) : a - b < c ↔ a < c + b := by
  rw [add_commₓ]
  exact hb.tsub_lt_iff_left hba

protected theorem lt_tsub_of_add_lt_right (hc : AddLeCancellable c) (h : a + c < b) : a < b - c := by
  apply lt_of_le_of_neₓ
  · rw [← add_tsub_cancel_of_le h.le, add_right_commₓ, add_assocₓ]
    rw [hc.add_tsub_assoc_of_le]
    refine' le_self_add
    refine' le_add_self
    
  · rintro rfl
    apply h.not_le
    exact le_tsub_add
    

protected theorem lt_tsub_of_add_lt_left (ha : AddLeCancellable a) (h : a + c < b) : c < b - a := by
  apply ha.lt_tsub_of_add_lt_right
  rwa [add_commₓ]

protected theorem tsub_lt_iff_tsub_lt (hb : AddLeCancellable b) (hc : AddLeCancellable c) (h₁ : b ≤ a) (h₂ : c ≤ a) :
    a - b < c ↔ a - c < b := by
  rw [hb.tsub_lt_iff_left h₁, hc.tsub_lt_iff_right h₂]

protected theorem le_tsub_iff_le_tsub (ha : AddLeCancellable a) (hc : AddLeCancellable c) (h₁ : a ≤ b) (h₂ : c ≤ b) :
    a ≤ b - c ↔ c ≤ b - a := by
  rw [ha.le_tsub_iff_left h₁, hc.le_tsub_iff_right h₂]

protected theorem lt_tsub_iff_right_of_le (hc : AddLeCancellable c) (h : c ≤ b) : a < b - c ↔ a + c < b := by
  refine' ⟨_, hc.lt_tsub_of_add_lt_right⟩
  intro h2
  refine' (add_le_of_le_tsub_right_of_le h h2.le).lt_of_ne _
  rintro rfl
  apply h2.not_le
  rw [hc.add_tsub_cancel_right]

protected theorem lt_tsub_iff_left_of_le (hc : AddLeCancellable c) (h : c ≤ b) : a < b - c ↔ c + a < b := by
  rw [add_commₓ]
  exact hc.lt_tsub_iff_right_of_le h

protected theorem lt_of_tsub_lt_tsub_left_of_le [ContravariantClass α α (· + ·) (· < ·)] (hb : AddLeCancellable b)
    (hca : c ≤ a) (h : a - b < a - c) : c < b := by
  conv_lhs at h => rw [← tsub_add_cancel_of_le hca]
  exact lt_of_add_lt_add_left (hb.lt_add_of_tsub_lt_right h)

protected theorem tsub_le_tsub_iff_left (ha : AddLeCancellable a) (hc : AddLeCancellable c) (h : c ≤ a) :
    a - b ≤ a - c ↔ c ≤ b := by
  refine' ⟨_, fun h => tsub_le_tsub_left h a⟩
  rw [tsub_le_iff_left, ← hc.add_tsub_assoc_of_le h, hc.le_tsub_iff_right (h.trans le_add_self), add_commₓ b]
  apply ha

protected theorem tsub_right_inj (ha : AddLeCancellable a) (hb : AddLeCancellable b) (hc : AddLeCancellable c)
    (hba : b ≤ a) (hca : c ≤ a) : a - b = a - c ↔ b = c := by
  simp_rw [le_antisymm_iffₓ, ha.tsub_le_tsub_iff_left hb hba, ha.tsub_le_tsub_iff_left hc hca, and_comm]

protected theorem tsub_lt_tsub_right_of_le (hc : AddLeCancellable c) (h : c ≤ a) (h2 : a < b) : a - c < b - c := by
  apply hc.lt_tsub_of_add_lt_left
  rwa [add_tsub_cancel_of_le h]

protected theorem tsub_inj_right (hab : AddLeCancellable (a - b)) (h₁ : b ≤ a) (h₂ : c ≤ a) (h₃ : a - b = a - c) :
    b = c := by
  rw [← hab.inj]
  rw [tsub_add_cancel_of_le h₁, h₃, tsub_add_cancel_of_le h₂]

protected theorem tsub_lt_tsub_iff_left_of_le_of_le [ContravariantClass α α (· + ·) (· < ·)] (hb : AddLeCancellable b)
    (hab : AddLeCancellable (a - b)) (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < a - c ↔ c < b := by
  refine' ⟨hb.lt_of_tsub_lt_tsub_left_of_le h₂, _⟩
  intro h
  refine' (tsub_le_tsub_left h.le _).lt_of_ne _
  rintro h2
  exact h.ne' (hab.tsub_inj_right h₁ h₂ h2)

@[simp]
protected theorem add_tsub_tsub_cancel (hac : AddLeCancellable (a - c)) (h : c ≤ a) : a + b - (a - c) = b + c :=
  (hac.tsub_eq_iff_eq_add_of_le <| tsub_le_self.trans le_self_add).mpr <| by
    rw [add_assocₓ, add_tsub_cancel_of_le h, add_commₓ]

protected theorem tsub_tsub_cancel_of_le (hba : AddLeCancellable (b - a)) (h : a ≤ b) : b - (b - a) = a := by
  rw [hba.tsub_eq_iff_eq_add_of_le tsub_le_self, add_tsub_cancel_of_le h]

end AddLeCancellable

section Contra

/-! ### Lemmas where addition is order-reflecting. -/


variable [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem eq_tsub_iff_add_eq_of_le (h : c ≤ b) : a = b - c ↔ a + c = b :=
  Contravariant.add_le_cancellable.eq_tsub_iff_add_eq_of_le h

theorem tsub_eq_iff_eq_add_of_le (h : b ≤ a) : a - b = c ↔ a = c + b :=
  Contravariant.add_le_cancellable.tsub_eq_iff_eq_add_of_le h

/-- See `add_tsub_le_assoc` for an inequality. -/
theorem add_tsub_assoc_of_le (h : c ≤ b) (a : α) : a + b - c = a + (b - c) :=
  Contravariant.add_le_cancellable.add_tsub_assoc_of_le h a

theorem tsub_add_eq_add_tsub (h : b ≤ a) : a - b + c = a + c - b :=
  Contravariant.add_le_cancellable.tsub_add_eq_add_tsub h

theorem tsub_tsub_assoc (h₁ : b ≤ a) (h₂ : c ≤ b) : a - (b - c) = a - b + c :=
  Contravariant.add_le_cancellable.tsub_tsub_assoc h₁ h₂

theorem tsub_add_tsub_comm (hba : b ≤ a) (hdc : d ≤ c) : a - b + (c - d) = a + c - (b + d) :=
  Contravariant.add_le_cancellable.tsub_add_tsub_comm Contravariant.add_le_cancellable hba hdc

theorem le_tsub_iff_left (h : a ≤ c) : b ≤ c - a ↔ a + b ≤ c :=
  Contravariant.add_le_cancellable.le_tsub_iff_left h

theorem le_tsub_iff_right (h : a ≤ c) : b ≤ c - a ↔ b + a ≤ c :=
  Contravariant.add_le_cancellable.le_tsub_iff_right h

theorem tsub_lt_iff_left (hbc : b ≤ a) : a - b < c ↔ a < b + c :=
  Contravariant.add_le_cancellable.tsub_lt_iff_left hbc

theorem tsub_lt_iff_right (hbc : b ≤ a) : a - b < c ↔ a < c + b :=
  Contravariant.add_le_cancellable.tsub_lt_iff_right hbc

/-- This lemma (and some of its corollaries also holds for `ennreal`,
  but this proof doesn't work for it.
  Maybe we should add this lemma as field to `has_ordered_sub`? -/
theorem lt_tsub_of_add_lt_right (h : a + c < b) : a < b - c :=
  Contravariant.add_le_cancellable.lt_tsub_of_add_lt_right h

theorem lt_tsub_of_add_lt_left (h : a + c < b) : c < b - a :=
  Contravariant.add_le_cancellable.lt_tsub_of_add_lt_left h

theorem tsub_lt_iff_tsub_lt (h₁ : b ≤ a) (h₂ : c ≤ a) : a - b < c ↔ a - c < b :=
  Contravariant.add_le_cancellable.tsub_lt_iff_tsub_lt Contravariant.add_le_cancellable h₁ h₂

theorem le_tsub_iff_le_tsub (h₁ : a ≤ b) (h₂ : c ≤ b) : a ≤ b - c ↔ c ≤ b - a :=
  Contravariant.add_le_cancellable.le_tsub_iff_le_tsub Contravariant.add_le_cancellable h₁ h₂

/-- See `lt_tsub_iff_right` for a stronger statement in a linear order. -/
theorem lt_tsub_iff_right_of_le (h : c ≤ b) : a < b - c ↔ a + c < b :=
  Contravariant.add_le_cancellable.lt_tsub_iff_right_of_le h

/-- See `lt_tsub_iff_left` for a stronger statement in a linear order. -/
theorem lt_tsub_iff_left_of_le (h : c ≤ b) : a < b - c ↔ c + a < b :=
  Contravariant.add_le_cancellable.lt_tsub_iff_left_of_le h

/-- See `lt_of_tsub_lt_tsub_left` for a stronger statement in a linear order. -/
theorem lt_of_tsub_lt_tsub_left_of_le [ContravariantClass α α (· + ·) (· < ·)] (hca : c ≤ a) (h : a - b < a - c) :
    c < b :=
  Contravariant.add_le_cancellable.lt_of_tsub_lt_tsub_left_of_le hca h

theorem tsub_le_tsub_iff_left (h : c ≤ a) : a - b ≤ a - c ↔ c ≤ b :=
  Contravariant.add_le_cancellable.tsub_le_tsub_iff_left Contravariant.add_le_cancellable h

theorem tsub_right_inj (hba : b ≤ a) (hca : c ≤ a) : a - b = a - c ↔ b = c :=
  Contravariant.add_le_cancellable.tsub_right_inj Contravariant.add_le_cancellable Contravariant.add_le_cancellable hba
    hca

theorem tsub_lt_tsub_right_of_le (h : c ≤ a) (h2 : a < b) : a - c < b - c :=
  Contravariant.add_le_cancellable.tsub_lt_tsub_right_of_le h h2

theorem tsub_inj_right (h₁ : b ≤ a) (h₂ : c ≤ a) (h₃ : a - b = a - c) : b = c :=
  Contravariant.add_le_cancellable.tsub_inj_right h₁ h₂ h₃

/-- See `tsub_lt_tsub_iff_left_of_le` for a stronger statement in a linear order. -/
theorem tsub_lt_tsub_iff_left_of_le_of_le [ContravariantClass α α (· + ·) (· < ·)] (h₁ : b ≤ a) (h₂ : c ≤ a) :
    a - b < a - c ↔ c < b :=
  Contravariant.add_le_cancellable.tsub_lt_tsub_iff_left_of_le_of_le Contravariant.add_le_cancellable h₁ h₂

@[simp]
theorem add_tsub_tsub_cancel (h : c ≤ a) : a + b - (a - c) = b + c :=
  Contravariant.add_le_cancellable.add_tsub_tsub_cancel h

/-- See `tsub_tsub_le` for an inequality. -/
theorem tsub_tsub_cancel_of_le (h : a ≤ b) : b - (b - a) = a :=
  Contravariant.add_le_cancellable.tsub_tsub_cancel_of_le h

end Contra

end CanonicallyOrderedAddMonoid

/-! ### Lemmas in a linearly canonically ordered monoid. -/


section CanonicallyLinearOrderedAddMonoid

variable [CanonicallyLinearOrderedAddMonoid α] [Sub α] [HasOrderedSub α] {a b c d : α}

@[simp]
theorem tsub_pos_iff_lt : 0 < a - b ↔ b < a := by
  rw [tsub_pos_iff_not_le, not_leₓ]

theorem tsub_eq_tsub_min (a b : α) : a - b = a - min a b := by
  cases' le_totalₓ a b with h h
  · rw [min_eq_leftₓ h, tsub_self, tsub_eq_zero_iff_le.mpr h]
    
  · rw [min_eq_rightₓ h]
    

namespace AddLeCancellable

protected theorem lt_tsub_iff_right (hc : AddLeCancellable c) : a < b - c ↔ a + c < b :=
  ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_right.mpr, hc.lt_tsub_of_add_lt_right⟩

protected theorem lt_tsub_iff_left (hc : AddLeCancellable c) : a < b - c ↔ c + a < b :=
  ⟨lt_imp_lt_of_le_imp_le tsub_le_iff_left.mpr, hc.lt_tsub_of_add_lt_left⟩

protected theorem tsub_lt_tsub_iff_right (hc : AddLeCancellable c) (h : c ≤ a) : a - c < b - c ↔ a < b := by
  rw [hc.lt_tsub_iff_left, add_tsub_cancel_of_le h]

protected theorem tsub_lt_self (ha : AddLeCancellable a) (h₁ : 0 < a) (h₂ : 0 < b) : a - b < a := by
  refine' tsub_le_self.lt_of_ne fun h => _
  rw [← h, tsub_pos_iff_lt] at h₁
  exact h₂.not_le (ha.add_le_iff_nonpos_left.1 <| add_le_of_le_tsub_left_of_le h₁.le h.ge)

protected theorem tsub_lt_self_iff (ha : AddLeCancellable a) : a - b < a ↔ 0 < a ∧ 0 < b := by
  refine' ⟨fun h => ⟨(zero_le _).trans_lt h, (zero_le b).lt_of_ne _⟩, fun h => ha.tsub_lt_self h.1 h.2⟩
  rintro rfl
  rw [tsub_zero] at h
  exact h.false

/-- See `lt_tsub_iff_left_of_le_of_le` for a weaker statement in a partial order. -/
protected theorem tsub_lt_tsub_iff_left_of_le (ha : AddLeCancellable a) (hb : AddLeCancellable b) (h : b ≤ a) :
    a - b < a - c ↔ c < b :=
  lt_iff_lt_of_le_iff_le <| ha.tsub_le_tsub_iff_left hb h

end AddLeCancellable

section Contra

variable [ContravariantClass α α (· + ·) (· ≤ ·)]

/-- This lemma also holds for `ennreal`, but we need a different proof for that. -/
theorem tsub_lt_tsub_iff_right (h : c ≤ a) : a - c < b - c ↔ a < b :=
  Contravariant.add_le_cancellable.tsub_lt_tsub_iff_right h

theorem tsub_lt_self : 0 < a → 0 < b → a - b < a :=
  Contravariant.add_le_cancellable.tsub_lt_self

theorem tsub_lt_self_iff : a - b < a ↔ 0 < a ∧ 0 < b :=
  Contravariant.add_le_cancellable.tsub_lt_self_iff

/-- See `lt_tsub_iff_left_of_le_of_le` for a weaker statement in a partial order. -/
theorem tsub_lt_tsub_iff_left_of_le (h : b ≤ a) : a - b < a - c ↔ c < b :=
  Contravariant.add_le_cancellable.tsub_lt_tsub_iff_left_of_le Contravariant.add_le_cancellable h

end Contra

/-! ### Lemmas about `max` and `min`. -/


theorem tsub_add_eq_max : a - b + b = max a b := by
  cases' le_totalₓ a b with h h
  · rw [max_eq_rightₓ h, tsub_eq_zero_iff_le.mpr h, zero_addₓ]
    
  · rw [max_eq_leftₓ h, tsub_add_cancel_of_le h]
    

theorem add_tsub_eq_max : a + (b - a) = max a b := by
  rw [add_commₓ, max_commₓ, tsub_add_eq_max]

theorem tsub_min : a - min a b = a - b := by
  cases' le_totalₓ a b with h h
  · rw [min_eq_leftₓ h, tsub_self, tsub_eq_zero_iff_le.mpr h]
    
  · rw [min_eq_rightₓ h]
    

theorem tsub_add_min : a - b + min a b = a := by
  rw [← tsub_min, tsub_add_cancel_of_le]
  apply min_le_leftₓ

end CanonicallyLinearOrderedAddMonoid

namespace WithTop

section

variable [Sub α] [Zero α]

/-- If `α` has subtraction and `0`, we can extend the subtraction to `with_top α`. -/
protected def sub : ∀ a b : WithTop α, WithTop α
  | _, ⊤ => 0
  | ⊤, (x : α) => ⊤
  | (x : α), (y : α) => (x - y : α)

instance : Sub (WithTop α) :=
  ⟨WithTop.sub⟩

@[simp, norm_cast]
theorem coe_sub {a b : α} : (↑(a - b) : WithTop α) = ↑a - ↑b :=
  rfl

@[simp]
theorem top_sub_coe {a : α} : (⊤ : WithTop α) - a = ⊤ :=
  rfl

@[simp]
theorem sub_top {a : WithTop α} : a - ⊤ = 0 := by
  cases a <;> rfl

end

variable [CanonicallyOrderedAddMonoid α] [Sub α] [HasOrderedSub α]

instance : HasOrderedSub (WithTop α) := by
  constructor
  rintro x y z
  induction y using WithTop.recTopCoe
  · simp
    
  induction x using WithTop.recTopCoe
  · simp
    
  induction z using WithTop.recTopCoe
  · simp
    
  norm_cast
  exact tsub_le_iff_right

end WithTop

