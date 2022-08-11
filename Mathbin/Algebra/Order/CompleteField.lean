/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
import Mathbin.Algebra.Order.Hom.Ring
import Mathbin.Algebra.Order.Pointwise
import Mathbin.Analysis.SpecialFunctions.Pow

/-!
# Conditionally complete linear ordered fields

This file shows that the reals are unique, or, more formally, given a type satisfying the common
axioms of the reals (field, conditionally complete, linearly ordered) that there is an isomorphism
preserving these properties to the reals. This is `rat.induced_order_ring_iso`. Moreover this
isomorphism is unique.

We introduce definitions of conditionally complete linear ordered fields, and show all such are
archimedean. We also construct the natural map from a `linear_ordered_field` to such a field.

## Main definitions

* `conditionally_complete_linear_ordered_field`: A field satisfying the standard axiomatization of
  the real numbers, being a Dedekind complete and linear ordered field.
* `linear_ordered_field.induced_map`: A (unique) map from any archimedean linear ordered field to a
  conditionally complete linear ordered field. Various bundlings are available.

## Main results

* `unique.order_ring_hom` : Uniqueness of `order_ring_hom`s from an archimedean linear ordered field
  to a conditionally complete linear ordered field.
* `unique.order_ring_iso` : Uniqueness of `order_ring_iso`s between two
  conditionally complete linearly ordered fields.

## References

* https://mathoverflow.net/questions/362991/
  who-first-characterized-the-real-numbers-as-the-unique-complete-ordered-field

## Tags

reals, conditionally complete, ordered field, uniqueness
-/


variable {F α β γ : Type _}

noncomputable section

open Function Rat Real Set

open Classical Pointwise

-- ./././Mathport/Syntax/Translate/Basic.lean:1467:11: unsupported: advanced extends in structure
/-- A field which is both linearly ordered and conditionally complete with respect to the order.
This axiomatizes the reals. -/
@[protect_proj, ancestor LinearOrderedField ConditionallyCompleteLinearOrder]
class ConditionallyCompleteLinearOrderedField (α : Type _) extends
  "./././Mathport/Syntax/Translate/Basic.lean:1467:11: unsupported: advanced extends in structure",
  ConditionallyCompleteLinearOrder α

/-- Any conditionally complete linearly ordered field is archimedean. -/
-- see Note [lower instance priority]
instance (priority := 100) ConditionallyCompleteLinearOrderedField.to_archimedean
    [ConditionallyCompleteLinearOrderedField α] : Archimedean α :=
  archimedean_iff_nat_lt.2
    (by
      by_contra' h
      obtain ⟨x, h⟩ := h
      have :=
        cSup_le (range_nonempty (coe : ℕ → α))
          (forall_range_iff.2 fun n =>
            le_sub_iff_add_le.2 <| le_cSup ⟨x, forall_range_iff.2 h⟩ ⟨n + 1, Nat.cast_succₓ n⟩)
      linarith)

/-- The reals are a conditionally complete linearly ordered field. -/
instance : ConditionallyCompleteLinearOrderedField ℝ :=
  { Real.linearOrderedField, Real.conditionallyCompleteLinearOrder with }

namespace LinearOrderedField

/-!
### Rational cut map

The idea is that a conditionally complete linear ordered field is fully characterized by its copy of
the rationals. Hence we define `rat.cut_map β : α → set β` which sends `a : α` to the "rationals in
`β`" that are less than `a`.
-/


section CutMap

variable [LinearOrderedField α]

section DivisionRing

variable (β) [DivisionRing β] {a a₁ a₂ : α} {b : β} {q : ℚ}

/-- The lower cut of rationals inside a linear ordered field that are less than a given element of
another linear ordered field. -/
def CutMap (a : α) : Set β :=
  (coe : ℚ → β) '' { t | ↑t < a }

theorem cut_map_mono (h : a₁ ≤ a₂) : CutMap β a₁ ⊆ CutMap β a₂ :=
  (image_subset _) fun _ => h.trans_lt'

variable {β}

@[simp]
theorem mem_cut_map_iff : b ∈ CutMap β a ↔ ∃ q : ℚ, (q : α) < a ∧ (q : β) = b :=
  Iff.rfl

@[simp]
theorem coe_mem_cut_map_iff [CharZero β] : (q : β) ∈ CutMap β a ↔ (q : α) < a :=
  Rat.cast_injective.mem_set_image

theorem cut_map_self (a : α) : CutMap α a = Iio a ∩ Range (coe : ℚ → α) := by
  ext
  constructor
  · rintro ⟨q, h, rfl⟩
    exact ⟨h, q, rfl⟩
    
  · rintro ⟨h, q, rfl⟩
    exact ⟨q, h, rfl⟩
    

end DivisionRing

variable (β) [LinearOrderedField β] {a a₁ a₂ : α} {b : β} {q : ℚ}

theorem cut_map_coe (q : ℚ) : CutMap β (q : α) = coe '' { r : ℚ | (r : β) < q } := by
  simp_rw [cut_map, Rat.cast_lt]

variable [Archimedean α]

theorem cut_map_nonempty (a : α) : (CutMap β a).Nonempty :=
  Nonempty.image _ <| exists_rat_lt a

theorem cut_map_bdd_above (a : α) : BddAbove (CutMap β a) := by
  obtain ⟨q, hq⟩ := exists_rat_gt a
  exact
    ⟨q,
      ball_image_iff.2 fun r hr => by
        exact_mod_cast (hq.trans' hr).le⟩

theorem cut_map_add (a b : α) : CutMap β (a + b) = CutMap β a + CutMap β b := by
  refine' (image_subset_iff.2 fun q hq => _).antisymm _
  · rw [mem_set_of_eq, ← sub_lt_iff_lt_add] at hq
    obtain ⟨q₁, hq₁q, hq₁ab⟩ := exists_rat_btwn hq
    refine' ⟨q₁, q - q₁, _, _, add_sub_cancel'_right _ _⟩ <;>
      try
          norm_cast <;>
        rwa [coe_mem_cut_map_iff]
    exact_mod_cast sub_lt.mp hq₁q
    
  · rintro _ ⟨_, _, ⟨qa, ha, rfl⟩, ⟨qb, hb, rfl⟩, rfl⟩
    refine'
      ⟨qa + qb, _, by
        norm_cast⟩
    rw [mem_set_of_eq, cast_add]
    exact add_lt_add ha hb
    

end CutMap

/-!
### Induced map

`rat.cut_map` spits out a `set β`. To get something in `β`, we now take the supremum.
-/


section InducedMap

variable (α β γ) [LinearOrderedField α] [ConditionallyCompleteLinearOrderedField β]
  [ConditionallyCompleteLinearOrderedField γ]

/-- The induced order preserving function from a linear ordered field to a conditionally complete
linear ordered field, defined by taking the Sup in the codomain of all the rationals less than the
input. -/
def inducedMap (x : α) : β :=
  Sup <| CutMap β x

variable [Archimedean α]

theorem induced_map_mono : Monotone (inducedMap α β) := fun a b h =>
  cSup_le_cSup (cut_map_bdd_above β _) (cut_map_nonempty β _) (cut_map_mono β h)

theorem induced_map_rat (q : ℚ) : inducedMap α β (q : α) = q := by
  refine' cSup_eq_of_forall_le_of_forall_lt_exists_gt (cut_map_nonempty β q) (fun x h => _) fun w h => _
  · rw [cut_map_coe] at h
    obtain ⟨r, h, rfl⟩ := h
    exact le_of_ltₓ h
    
  · obtain ⟨q', hwq, hq⟩ := exists_rat_btwn h
    rw [cut_map_coe]
    exact ⟨q', ⟨_, hq, rfl⟩, hwq⟩
    

@[simp]
theorem induced_map_zero : inducedMap α β 0 = 0 := by
  exact_mod_cast induced_map_rat α β 0

@[simp]
theorem induced_map_one : inducedMap α β 1 = 1 := by
  exact_mod_cast induced_map_rat α β 1

variable {α β} {a : α} {b : β} {q : ℚ}

theorem induced_map_nonneg (ha : 0 ≤ a) : 0 ≤ inducedMap α β a :=
  (induced_map_zero α _).Ge.trans <| induced_map_mono _ _ ha

theorem coe_lt_induced_map_iff : (q : β) < inducedMap α β a ↔ (q : α) < a := by
  refine' ⟨fun h => _, fun hq => _⟩
  · rw [← induced_map_rat α] at h
    exact (induced_map_mono α β).reflect_lt h
    
  · obtain ⟨q', hq, hqa⟩ := exists_rat_btwn hq
    apply lt_cSup_of_lt (cut_map_bdd_above β a) (coe_mem_cut_map_iff.mpr hqa)
    exact_mod_cast hq
    

theorem lt_induced_map_iff : b < inducedMap α β a ↔ ∃ q : ℚ, b < q ∧ (q : α) < a :=
  ⟨fun h => (exists_rat_btwn h).imp fun q => And.imp_right coe_lt_induced_map_iff.1, fun ⟨q, hbq, hqa⟩ =>
    hbq.trans <| by
      rwa [coe_lt_induced_map_iff]⟩

@[simp]
theorem induced_map_self (b : β) : inducedMap β β b = b :=
  eq_of_forall_rat_lt_iff_lt fun q => coe_lt_induced_map_iff

variable (α β)

@[simp]
theorem induced_map_induced_map (a : α) : inducedMap β γ (inducedMap α β a) = inducedMap α γ a :=
  eq_of_forall_rat_lt_iff_lt fun q => by
    rw [coe_lt_induced_map_iff, coe_lt_induced_map_iff, Iff.comm, coe_lt_induced_map_iff]

@[simp]
theorem induced_map_inv_self (b : β) : inducedMap γ β (inducedMap β γ b) = b := by
  rw [induced_map_induced_map, induced_map_self]

theorem induced_map_add (x y : α) : inducedMap α β (x + y) = inducedMap α β x + inducedMap α β y := by
  rw [induced_map, cut_map_add]
  exact cSup_add (cut_map_nonempty β x) (cut_map_bdd_above β x) (cut_map_nonempty β y) (cut_map_bdd_above β y)

variable {α β}

/-- Preparatory lemma for `induced_ring_hom`. -/
theorem le_induced_map_mul_self_of_mem_cut_map (ha : 0 < a) (b : β) (hb : b ∈ CutMap β (a * a)) :
    b ≤ inducedMap α β a * inducedMap α β a := by
  obtain ⟨q, hb, rfl⟩ := hb
  obtain ⟨q', hq', hqq', hqa⟩ := exists_rat_pow_btwn two_ne_zero hb (mul_self_pos.2 ha.ne')
  trans (q' : β) ^ 2
  exact_mod_cast hqq'.le
  rw [pow_two] at hqa⊢
  exact
    mul_self_le_mul_self
      (by
        exact_mod_cast hq'.le)
      (le_cSup (cut_map_bdd_above β a) <| coe_mem_cut_map_iff.2 <| lt_of_mul_self_lt_mul_self ha.le hqa)

/-- Preparatory lemma for `induced_ring_hom`. -/
theorem exists_mem_cut_map_mul_self_of_lt_induced_map_mul_self (ha : 0 < a) (b : β)
    (hba : b < inducedMap α β a * inducedMap α β a) : ∃ c ∈ CutMap β (a * a), b < c := by
  obtain hb | hb := lt_or_leₓ b 0
  · refine' ⟨0, _, hb⟩
    rw [← Rat.cast_zero, coe_mem_cut_map_iff, Rat.cast_zero]
    exact mul_self_pos.2 ha.ne'
    
  obtain ⟨q, hq, hbq, hqa⟩ := exists_rat_pow_btwn two_ne_zero hba (hb.trans_lt hba)
  rw [← cast_pow] at hbq
  refine' ⟨(q ^ 2 : ℚ), coe_mem_cut_map_iff.2 _, hbq⟩
  rw [pow_two] at hqa⊢
  push_cast
  obtain ⟨q', hq', hqa'⟩ := lt_induced_map_iff.1 (lt_of_mul_self_lt_mul_self _ hqa)
  exact
    mul_self_lt_mul_self
      (by
        exact_mod_cast hq.le)
      (hqa'.trans' <| by
        assumption_mod_cast)
  exact induced_map_nonneg ha.le

variable (α β)

/-- `induced_map` as an additive homomorphism. -/
def inducedAddHom : α →+ β :=
  ⟨inducedMap α β, induced_map_zero α β, induced_map_add α β⟩

/-- `induced_map` as an `order_ring_hom`. -/
@[simps]
def inducedOrderRingHom : α →+*o β :=
  { (inducedAddHom α β).mkRingHomOfMulSelfOfTwoNeZero
      (-- reduce to the case of x = y
      by
        -- reduce to the case of 0 < x
        suffices ∀ x, 0 < x → induced_add_hom α β (x * x) = induced_add_hom α β x * induced_add_hom α β x by
          rintro x
          obtain h | rfl | h := lt_trichotomyₓ x 0
          · convert this (-x) (neg_pos.2 h) using 1
            · rw [neg_mul, mul_neg, neg_negₓ]
              
            · simp_rw [AddMonoidHom.map_neg, neg_mul, mul_neg, neg_negₓ]
              
            
          · simp only [← mul_zero, ← AddMonoidHom.map_zero]
            
          · exact this x h
            
        -- prove that the (Sup of rationals less than x) ^ 2 is the Sup of the set of rationals less
        -- than (x ^ 2) by showing it is an upper bound and any smaller number is not an upper bound
        refine' fun x hx => cSup_eq_of_forall_le_of_forall_lt_exists_gt (cut_map_nonempty β _) _ _
        exact le_induced_map_mul_self_of_mem_cut_map hx
        exact exists_mem_cut_map_mul_self_of_lt_induced_map_mul_self hx)
      two_ne_zero (induced_map_one _ _) with
    monotone' := induced_map_mono _ _ }

/-- The isomorphism of ordered rings between two conditionally complete linearly ordered fields. -/
def inducedOrderRingIso : β ≃+*o γ :=
  { inducedOrderRingHom β γ with invFun := inducedMap γ β, left_inv := induced_map_inv_self _ _,
    right_inv := induced_map_inv_self _ _,
    map_le_map_iff' := fun x y => by
      refine' ⟨fun h => _, fun h => induced_map_mono _ _ h⟩
      simpa [← induced_order_ring_hom, ← AddMonoidHom.mkRingHomOfMulSelfOfTwoNeZero, ← induced_add_hom] using
        induced_map_mono γ β h }

@[simp]
theorem coe_induced_order_ring_iso : ⇑(inducedOrderRingIso β γ) = inducedMap β γ :=
  rfl

@[simp]
theorem induced_order_ring_iso_symm : (inducedOrderRingIso β γ).symm = inducedOrderRingIso γ β :=
  rfl

@[simp]
theorem induced_order_ring_iso_self : inducedOrderRingIso β β = OrderRingIso.refl β :=
  OrderRingIso.ext induced_map_self

open OrderRingIso

attribute [local instance] OrderRingHom.subsingleton OrderRingIso.subsingleton_left

/-- There is a unique ordered ring homomorphism from an archimedean linear ordered field to a
conditionally complete linear ordered field. -/
instance : Unique (α →+*o β) :=
  uniqueOfSubsingleton <| inducedOrderRingHom α β

/-- There is a unique ordered ring isomorphism between two conditionally complete linear ordered
fields. -/
instance : Unique (β ≃+*o γ) :=
  uniqueOfSubsingleton <| inducedOrderRingIso β γ

end InducedMap

end LinearOrderedField

