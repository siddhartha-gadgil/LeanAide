/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathbin.Algebra.Order.Field
import Mathbin.Algebra.SmulWithZero
import Mathbin.GroupTheory.GroupAction.Group

/-!
# Ordered scalar product

In this file we define

* `ordered_smul R M` : an ordered additive commutative monoid `M` is an `ordered_smul`
  over an `ordered_semiring` `R` if the scalar product respects the order relation on the
  monoid and on the ring. There is a correspondence between this structure and convex cones,
  which is proven in `analysis/convex/cone.lean`.

## Implementation notes

* We choose to define `ordered_smul` as a `Prop`-valued mixin, so that it can be
  used for actions, modules, and algebras
  (the axioms for an "ordered algebra" are exactly that the algebra is ordered as a module).
* To get ordered modules and ordered vector spaces, it suffices to replace the
  `order_add_comm_monoid` and the `ordered_semiring` as desired.

## References

* https://en.wikipedia.org/wiki/Ordered_module

## Tags

ordered module, ordered scalar, ordered smul, ordered action, ordered vector space
-/


/-- The ordered scalar product property is when an ordered additive commutative monoid
with a partial order has a scalar multiplication which is compatible with the order.
-/
@[protect_proj]
class OrderedSmul (R M : Type _) [OrderedSemiring R] [OrderedAddCommMonoid M] [SmulWithZero R M] : Prop where
  smul_lt_smul_of_pos : ∀ {a b : M}, ∀ {c : R}, a < b → 0 < c → c • a < c • b
  lt_of_smul_lt_smul_of_pos : ∀ {a b : M}, ∀ {c : R}, c • a < c • b → 0 < c → a < b

namespace OrderDual

variable {R M : Type _}

instance [HasSmul R M] : HasSmul R Mᵒᵈ :=
  ⟨fun k x => OrderDual.rec (fun x' => (k • x' : M)) x⟩

instance [Zero R] [AddZeroClassₓ M] [h : SmulWithZero R M] : SmulWithZero R Mᵒᵈ :=
  { OrderDual.hasSmul with zero_smul := fun m => OrderDual.rec (zero_smul _) m,
    smul_zero := fun r => OrderDual.rec (smul_zero' _) r }

instance [Monoidₓ R] [MulAction R M] : MulAction R Mᵒᵈ :=
  { OrderDual.hasSmul with one_smul := fun m => OrderDual.rec (one_smul _) m,
    mul_smul := fun r => OrderDual.rec mul_smul r }

instance [MonoidWithZeroₓ R] [AddMonoidₓ M] [MulActionWithZero R M] : MulActionWithZero R Mᵒᵈ :=
  { OrderDual.mulAction, OrderDual.smulWithZero with }

instance [MonoidWithZeroₓ R] [AddMonoidₓ M] [DistribMulAction R M] : DistribMulAction R Mᵒᵈ where
  smul_add := fun k a => OrderDual.rec (fun a' b => OrderDual.rec (smul_add _ _) b) a
  smul_zero := fun r => OrderDual.rec smul_zero r

instance [OrderedSemiring R] [OrderedAddCommMonoid M] [SmulWithZero R M] [OrderedSmul R M] : OrderedSmul R Mᵒᵈ where
  smul_lt_smul_of_pos := fun a b => @OrderedSmul.smul_lt_smul_of_pos R M _ _ _ _ b a
  lt_of_smul_lt_smul_of_pos := fun a b => @OrderedSmul.lt_of_smul_lt_smul_of_pos R M _ _ _ _ b a

@[simp]
theorem to_dual_smul [HasSmul R M] {c : R} {a : M} : toDual (c • a) = c • toDual a :=
  rfl

@[simp]
theorem of_dual_smul [HasSmul R M] {c : R} {a : Mᵒᵈ} : ofDual (c • a) = c • ofDual a :=
  rfl

end OrderDual

section OrderedSmul

variable {R M : Type _} [OrderedSemiring R] [OrderedAddCommMonoid M] [SmulWithZero R M] [OrderedSmul R M] {a b : M}
  {c : R}

theorem smul_lt_smul_of_pos : a < b → 0 < c → c • a < c • b :=
  OrderedSmul.smul_lt_smul_of_pos

theorem smul_le_smul_of_nonneg (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c • a ≤ c • b := by
  rcases h₁.eq_or_lt with (rfl | hab)
  · rfl
    
  · rcases h₂.eq_or_lt with (rfl | hc)
    · rw [zero_smul, zero_smul]
      
    · exact (smul_lt_smul_of_pos hab hc).le
      
    

theorem smul_nonneg (hc : 0 ≤ c) (ha : 0 ≤ a) : 0 ≤ c • a :=
  calc
    (0 : M) = c • (0 : M) := (smul_zero' M c).symm
    _ ≤ c • a := smul_le_smul_of_nonneg ha hc
    

theorem smul_nonpos_of_nonneg_of_nonpos (hc : 0 ≤ c) (ha : a ≤ 0) : c • a ≤ 0 :=
  @smul_nonneg R Mᵒᵈ _ _ _ _ _ _ hc ha

theorem eq_of_smul_eq_smul_of_pos_of_le (h₁ : c • a = c • b) (hc : 0 < c) (hle : a ≤ b) : a = b :=
  hle.lt_or_eq.resolve_left fun hlt => (smul_lt_smul_of_pos hlt hc).Ne h₁

theorem lt_of_smul_lt_smul_of_nonneg (h : c • a < c • b) (hc : 0 ≤ c) : a < b :=
  hc.eq_or_lt.elim
    (fun hc =>
      False.elim <|
        lt_irreflₓ (0 : M) <| by
          rwa [← hc, zero_smul, zero_smul] at h)
    (OrderedSmul.lt_of_smul_lt_smul_of_pos h)

theorem smul_lt_smul_iff_of_pos (hc : 0 < c) : c • a < c • b ↔ a < b :=
  ⟨fun h => lt_of_smul_lt_smul_of_nonneg h hc.le, fun h => smul_lt_smul_of_pos h hc⟩

theorem smul_pos_iff_of_pos (hc : 0 < c) : 0 < c • a ↔ 0 < a :=
  calc
    0 < c • a ↔ c • 0 < c • a := by
      rw [smul_zero']
    _ ↔ 0 < a := smul_lt_smul_iff_of_pos hc
    

alias smul_pos_iff_of_pos ↔ _ smul_pos

theorem monotone_smul_left (hc : 0 ≤ c) : Monotone (HasSmul.smul c : M → M) := fun a b h => smul_le_smul_of_nonneg h hc

theorem strict_mono_smul_left (hc : 0 < c) : StrictMono (HasSmul.smul c : M → M) := fun a b h =>
  smul_lt_smul_of_pos h hc

end OrderedSmul

/-- If `R` is a linear ordered semifield, then it suffices to verify only the first axiom of
`ordered_smul`. Moreover, it suffices to verify that `a < b` and `0 < c` imply
`c • a ≤ c • b`. We have no semifields in `mathlib`, so we use the assumption `∀ c ≠ 0, is_unit c`
instead. -/
theorem OrderedSmul.mk'' {R M : Type _} [LinearOrderedSemiring R] [OrderedAddCommMonoid M] [MulActionWithZero R M]
    (hR : ∀ {c : R}, c ≠ 0 → IsUnit c) (hlt : ∀ ⦃a b : M⦄ ⦃c : R⦄, a < b → 0 < c → c • a ≤ c • b) : OrderedSmul R M :=
  by
  have hlt' : ∀ ⦃a b : M⦄ ⦃c : R⦄, a < b → 0 < c → c • a < c • b := by
    refine' fun a b c hab hc => (hlt hab hc).lt_of_ne _
    rw [Ne.def, (hR hc.ne').smul_left_cancel]
    exact hab.ne
  refine' { smul_lt_smul_of_pos := hlt'.. }
  intro a b c h hc
  rcases hR hc.ne' with ⟨c, rfl⟩
  rw [← inv_smul_smul c a, ← inv_smul_smul c b]
  refine' hlt' h (pos_of_mul_pos_right _ hc.le)
  simp only [← c.mul_inv, ← zero_lt_one]

/-- If `R` is a linear ordered field, then it suffices to verify only the first axiom of
`ordered_smul`. -/
theorem OrderedSmul.mk' {k M : Type _} [LinearOrderedField k] [OrderedAddCommMonoid M] [MulActionWithZero k M]
    (hlt : ∀ ⦃a b : M⦄ ⦃c : k⦄, a < b → 0 < c → c • a ≤ c • b) : OrderedSmul k M :=
  OrderedSmul.mk'' (fun c hc => IsUnit.mk0 _ hc) hlt

instance LinearOrderedSemiring.to_ordered_smul {R : Type _} [LinearOrderedSemiring R] : OrderedSmul R R where
  smul_lt_smul_of_pos := OrderedSemiring.mul_lt_mul_of_pos_left
  lt_of_smul_lt_smul_of_pos := fun _ _ _ h hc => lt_of_mul_lt_mul_left h hc.le

section Field

variable {k M : Type _} [LinearOrderedField k] [OrderedAddCommGroup M] [MulActionWithZero k M] [OrderedSmul k M]
  {a b : M} {c : k}

theorem smul_le_smul_iff_of_pos (hc : 0 < c) : c • a ≤ c • b ↔ a ≤ b :=
  ⟨fun h => inv_smul_smul₀ hc.ne' a ▸ inv_smul_smul₀ hc.ne' b ▸ smul_le_smul_of_nonneg h (inv_nonneg.2 hc.le), fun h =>
    smul_le_smul_of_nonneg h hc.le⟩

theorem smul_lt_iff_of_pos (hc : 0 < c) : c • a < b ↔ a < c⁻¹ • b :=
  calc
    c • a < b ↔ c • a < c • c⁻¹ • b := by
      rw [smul_inv_smul₀ hc.ne']
    _ ↔ a < c⁻¹ • b := smul_lt_smul_iff_of_pos hc
    

theorem lt_smul_iff_of_pos (hc : 0 < c) : a < c • b ↔ c⁻¹ • a < b :=
  calc
    a < c • b ↔ c • c⁻¹ • a < c • b := by
      rw [smul_inv_smul₀ hc.ne']
    _ ↔ c⁻¹ • a < b := smul_lt_smul_iff_of_pos hc
    

theorem smul_le_iff_of_pos (hc : 0 < c) : c • a ≤ b ↔ a ≤ c⁻¹ • b :=
  calc
    c • a ≤ b ↔ c • a ≤ c • c⁻¹ • b := by
      rw [smul_inv_smul₀ hc.ne']
    _ ↔ a ≤ c⁻¹ • b := smul_le_smul_iff_of_pos hc
    

theorem le_smul_iff_of_pos (hc : 0 < c) : a ≤ c • b ↔ c⁻¹ • a ≤ b :=
  calc
    a ≤ c • b ↔ c • c⁻¹ • a ≤ c • b := by
      rw [smul_inv_smul₀ hc.ne']
    _ ↔ c⁻¹ • a ≤ b := smul_le_smul_iff_of_pos hc
    

variable (M)

/-- Left scalar multiplication as an order isomorphism. -/
@[simps]
def OrderIso.smulLeft {c : k} (hc : 0 < c) : M ≃o M where
  toFun := fun b => c • b
  invFun := fun b => c⁻¹ • b
  left_inv := inv_smul_smul₀ hc.ne'
  right_inv := smul_inv_smul₀ hc.ne'
  map_rel_iff' := fun b₁ b₂ => smul_le_smul_iff_of_pos hc

end Field

