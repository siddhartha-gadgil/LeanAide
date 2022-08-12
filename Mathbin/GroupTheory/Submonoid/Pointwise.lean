/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Data.Set.Pointwise
import Mathbin.GroupTheory.Submonoid.Membership

/-! # Pointwise instances on `submonoid`s and `add_submonoid`s

This file provides:

* `submonoid.has_inv`
* `add_submonoid.has_neg`

and the actions

* `submonoid.pointwise_mul_action`
* `add_submonoid.pointwise_mul_action`

which matches the action of `mul_action_set`.

These are all available in the `pointwise` locale.

Additionally, it provides various degrees of monoid structure:
* `add_submonoid.has_one`
* `add_submonoid.has_mul`
* `add_submonoid.mul_one_class`
* `add_submonoid.semigroup`
* `add_submonoid.monoid`
which is available globally to match the monoid structure implied by `submodule.semiring`.

## Implementation notes

Most of the lemmas in this file are direct copies of lemmas from `algebra/pointwise.lean`.
While the statements of these lemmas are defeq, we repeat them here due to them not being
syntactically equal. Before adding new lemmas here, consider if they would also apply to the action
on `set`s.

-/


open Set

variable {α : Type _} {G : Type _} {M : Type _} {R : Type _} {A : Type _}

variable [Monoidₓ M] [AddMonoidₓ A]

namespace Submonoid

variable [Groupₓ G]

open Pointwise

/-- The submonoid with every element inverted. -/
@[to_additive " The additive submonoid with every element negated. "]
protected def hasInv :
    Inv (Submonoid G) where inv := fun S =>
    { Carrier := (S : Set G)⁻¹,
      one_mem' :=
        show (1 : G)⁻¹ ∈ S by
          rw [inv_one]
          exact S.one_mem,
      mul_mem' := fun a b (ha : a⁻¹ ∈ S) (hb : b⁻¹ ∈ S) =>
        show (a * b)⁻¹ ∈ S by
          rw [mul_inv_rev]
          exact S.mul_mem hb ha }

localized [Pointwise] attribute [instance] Submonoid.hasInv

open Pointwise

@[simp, to_additive]
theorem coe_inv (S : Submonoid G) : ↑S⁻¹ = (S : Set G)⁻¹ :=
  rfl

@[simp, to_additive]
theorem mem_inv {g : G} {S : Submonoid G} : g ∈ S⁻¹ ↔ g⁻¹ ∈ S :=
  Iff.rfl

@[to_additive]
instance : HasInvolutiveInv (Submonoid G) :=
  (SetLike.coe_injective.HasInvolutiveInv _) fun _ => rfl

@[simp, to_additive]
theorem inv_le_inv (S T : Submonoid G) : S⁻¹ ≤ T⁻¹ ↔ S ≤ T :=
  SetLike.coe_subset_coe.symm.trans Set.inv_subset_inv

@[to_additive]
theorem inv_le (S T : Submonoid G) : S⁻¹ ≤ T ↔ S ≤ T⁻¹ :=
  SetLike.coe_subset_coe.symm.trans Set.inv_subset

/-- `submonoid.has_inv` as an order isomorphism. -/
@[to_additive " `add_submonoid.has_neg` as an order isomorphism ", simps]
def invOrderIso : Submonoid G ≃o Submonoid G where
  toEquiv := Equivₓ.inv _
  map_rel_iff' := inv_le_inv

@[to_additive]
theorem closure_inv (s : Set G) : closure s⁻¹ = (closure s)⁻¹ := by
  apply le_antisymmₓ
  · rw [closure_le, coe_inv, ← Set.inv_subset, inv_invₓ]
    exact subset_closure
    
  · rw [inv_le, closure_le, coe_inv, ← Set.inv_subset]
    exact subset_closure
    

@[simp, to_additive]
theorem inv_inf (S T : Submonoid G) : (S⊓T)⁻¹ = S⁻¹⊓T⁻¹ :=
  SetLike.coe_injective Set.inter_inv

@[simp, to_additive]
theorem inv_sup (S T : Submonoid G) : (S⊔T)⁻¹ = S⁻¹⊔T⁻¹ :=
  (invOrderIso : Submonoid G ≃o Submonoid G).map_sup S T

@[simp, to_additive]
theorem inv_bot : (⊥ : Submonoid G)⁻¹ = ⊥ :=
  SetLike.coe_injective <| (Set.inv_singleton 1).trans <| congr_arg _ inv_one

@[simp, to_additive]
theorem inv_top : (⊤ : Submonoid G)⁻¹ = ⊤ :=
  SetLike.coe_injective <| Set.inv_univ

@[simp, to_additive]
theorem inv_infi {ι : Sort _} (S : ι → Submonoid G) : (⨅ i, S i)⁻¹ = ⨅ i, (S i)⁻¹ :=
  (invOrderIso : Submonoid G ≃o Submonoid G).map_infi _

@[simp, to_additive]
theorem inv_supr {ι : Sort _} (S : ι → Submonoid G) : (⨆ i, S i)⁻¹ = ⨆ i, (S i)⁻¹ :=
  (invOrderIso : Submonoid G ≃o Submonoid G).map_supr _

end Submonoid

namespace Submonoid

section Monoidₓ

variable [Monoidₓ α] [MulDistribMulAction α M]

/-- The action on a submonoid corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwiseMulAction : MulAction α (Submonoid M) where
  smul := fun a S => S.map (MulDistribMulAction.toMonoidEnd _ M a)
  one_smul := fun S => by
    ext
    simp
  mul_smul := fun a₁ a₂ S =>
    (congr_arg (fun f : Monoidₓ.End M => S.map f) (MonoidHom.map_mul _ _ _)).trans (S.map_map _ _).symm

localized [Pointwise] attribute [instance] Submonoid.pointwiseMulAction

open Pointwise

@[simp]
theorem coe_pointwise_smul (a : α) (S : Submonoid M) : ↑(a • S) = a • (S : Set M) :=
  rfl

theorem smul_mem_pointwise_smul (m : M) (a : α) (S : Submonoid M) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set M))

theorem mem_smul_pointwise_iff_exists (m : M) (a : α) (S : Submonoid M) : m ∈ a • S ↔ ∃ s : M, s ∈ S ∧ a • s = m :=
  (Set.mem_smul_set : m ∈ a • (S : Set M) ↔ _)

instance pointwise_central_scalar [MulDistribMulAction αᵐᵒᵖ M] [IsCentralScalar α M] :
    IsCentralScalar α (Submonoid M) :=
  ⟨fun a S => (congr_arg fun f : Monoidₓ.End M => S.map f) <| MonoidHom.ext <| op_smul_eq_smul _⟩

end Monoidₓ

section Groupₓ

variable [Groupₓ α] [MulDistribMulAction α M]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff

theorem mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : Submonoid M} {x : M} : x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem

theorem mem_inv_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {a : α} {S T : Submonoid M} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff

theorem pointwise_smul_subset_iff {a : α} {S T : Submonoid M} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff

theorem subset_pointwise_smul_iff {a : α} {S T : Submonoid M} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff

end Groupₓ

section GroupWithZeroₓ

variable [GroupWithZeroₓ α] [MulDistribMulAction α M]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : Submonoid M) (x : M) : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set M) x

theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (S : Submonoid M) (x : M) : x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set M) x

theorem mem_inv_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : Submonoid M) (x : M) : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set M) x

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : Submonoid M} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff₀ ha

theorem pointwise_smul_le_iff₀ {a : α} (ha : a ≠ 0) {S T : Submonoid M} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff₀ ha

theorem le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : Submonoid M} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff₀ ha

end GroupWithZeroₓ

open Pointwise

@[to_additive]
theorem mem_closure_inv {G : Type _} [Groupₓ G] (S : Set G) (x : G) :
    x ∈ Submonoid.closure S⁻¹ ↔ x⁻¹ ∈ Submonoid.closure S := by
  rw [closure_inv, mem_inv]

end Submonoid

namespace AddSubmonoid

section Monoidₓ

variable [Monoidₓ α] [DistribMulAction α A]

/-- The action on an additive submonoid corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwiseMulAction : MulAction α (AddSubmonoid A) where
  smul := fun a S => S.map (DistribMulAction.toAddMonoidEnd _ A a)
  one_smul := fun S => (congr_arg (fun f : AddMonoidₓ.End A => S.map f) (MonoidHom.map_one _)).trans S.map_id
  mul_smul := fun a₁ a₂ S =>
    (congr_arg (fun f : AddMonoidₓ.End A => S.map f) (MonoidHom.map_mul _ _ _)).trans (S.map_map _ _).symm

localized [Pointwise] attribute [instance] AddSubmonoid.pointwiseMulAction

open Pointwise

@[simp]
theorem coe_pointwise_smul (a : α) (S : AddSubmonoid A) : ↑(a • S) = a • (S : Set A) :=
  rfl

theorem smul_mem_pointwise_smul (m : A) (a : α) (S : AddSubmonoid A) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set A))

instance pointwise_central_scalar [DistribMulAction αᵐᵒᵖ A] [IsCentralScalar α A] :
    IsCentralScalar α (AddSubmonoid A) :=
  ⟨fun a S => (congr_arg fun f : AddMonoidₓ.End A => S.map f) <| AddMonoidHom.ext <| op_smul_eq_smul _⟩

end Monoidₓ

section Groupₓ

variable [Groupₓ α] [DistribMulAction α A]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff {a : α} {S : AddSubmonoid A} {x : A} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff

theorem mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : AddSubmonoid A} {x : A} : x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem

theorem mem_smul_pointwise_iff_exists (m : A) (a : α) (S : AddSubmonoid A) : m ∈ a • S ↔ ∃ s : A, s ∈ S ∧ a • s = m :=
  (Set.mem_smul_set : m ∈ a • (S : Set A) ↔ _)

theorem mem_inv_pointwise_smul_iff {a : α} {S : AddSubmonoid A} {x : A} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {a : α} {S T : AddSubmonoid A} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff

theorem pointwise_smul_le_iff {a : α} {S T : AddSubmonoid A} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff

theorem le_pointwise_smul_iff {a : α} {S T : AddSubmonoid A} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff

end Groupₓ

section GroupWithZeroₓ

variable [GroupWithZeroₓ α] [DistribMulAction α A]

open Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set A) x

theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set A) x

theorem mem_inv_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set A) x

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : AddSubmonoid A} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff₀ ha

theorem pointwise_smul_le_iff₀ {a : α} (ha : a ≠ 0) {S T : AddSubmonoid A} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff₀ ha

theorem le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : AddSubmonoid A} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff₀ ha

end GroupWithZeroₓ

end AddSubmonoid

/-! ### Elementwise monoid structure of additive submonoids

These definitions are a cut-down versions of the ones around `submodule.has_mul`, as that API is
usually more useful. -/


namespace AddSubmonoid

open Pointwise

section AddMonoidWithOneₓ

variable [AddMonoidWithOneₓ R]

instance : One (AddSubmonoid R) :=
  ⟨(Nat.castAddMonoidHom R).mrange⟩

theorem one_eq_mrange : (1 : AddSubmonoid R) = (Nat.castAddMonoidHom R).mrange :=
  rfl

theorem nat_cast_mem_one (n : ℕ) : (n : R) ∈ (1 : AddSubmonoid R) :=
  ⟨_, rfl⟩

@[simp]
theorem mem_one {x : R} : x ∈ (1 : AddSubmonoid R) ↔ ∃ n : ℕ, ↑n = x :=
  Iff.rfl

theorem one_eq_closure : (1 : AddSubmonoid R) = closure {1} := by
  simp only [← closure_singleton_eq, ← mul_oneₓ, ← one_eq_mrange]
  congr 1 with n
  simp

theorem one_eq_closure_one_set : (1 : AddSubmonoid R) = closure 1 :=
  one_eq_closure

end AddMonoidWithOneₓ

section NonUnitalNonAssocSemiringₓ

variable [NonUnitalNonAssocSemiringₓ R]

/-- Multiplication of additive submonoids of a semiring R. The additive submonoid `S * T` is the
smallest R-submodule of `R` containing the elements `s * t` for `s ∈ S` and `t ∈ T`. -/
instance : Mul (AddSubmonoid R) :=
  ⟨fun M N => ⨆ s : M, N.map <| AddMonoidHom.mul s.1⟩

theorem mul_mem_mul {M N : AddSubmonoid R} {m n : R} (hm : m ∈ M) (hn : n ∈ N) : m * n ∈ M * N :=
  (le_supr _ ⟨m, hm⟩ : _ ≤ M * N) ⟨n, hn, rfl⟩

theorem mul_le {M N P : AddSubmonoid R} : M * N ≤ P ↔ ∀, ∀ m ∈ M, ∀, ∀ n ∈ N, ∀, m * n ∈ P :=
  ⟨fun H m hm n hn => H <| mul_mem_mul hm hn, fun H =>
    supr_le fun ⟨m, hm⟩ => map_le_iff_le_comap.2 fun n hn => H m hm n hn⟩

@[elab_as_eliminator]
protected theorem mul_induction_on {M N : AddSubmonoid R} {C : R → Prop} {r : R} (hr : r ∈ M * N)
    (hm : ∀, ∀ m ∈ M, ∀, ∀ n ∈ N, ∀, C (m * n)) (ha : ∀ x y, C x → C y → C (x + y)) : C r :=
  (@mul_le _ _ _ _
        ⟨C, ha, by
          simpa only [← zero_mul] using hm _ (zero_mem _) _ (zero_mem _)⟩).2
    hm hr

open Pointwise

-- this proof is copied directly from `submodule.span_mul_span`
theorem closure_mul_closure (S T : Set R) : closure S * closure T = closure (S * T) := by
  apply le_antisymmₓ
  · rw [mul_le]
    intro a ha b hb
    apply closure_induction ha
    on_goal 1 =>
      intros
      apply closure_induction hb
      on_goal 1 =>
        intros
        exact subset_closure ⟨_, _, ‹_›, ‹_›, rfl⟩
    all_goals
      intros
      simp only [← mul_zero, ← zero_mul, ← zero_mem, ← left_distrib, ← right_distrib, ← mul_smul_comm, ← smul_mul_assoc]
      solve_by_elim [← add_mem _ _, ← zero_mem _]
    
  · rw [closure_le]
    rintro _ ⟨a, b, ha, hb, rfl⟩
    exact mul_mem_mul (subset_closure ha) (subset_closure hb)
    

theorem mul_eq_closure_mul_set (M N : AddSubmonoid R) : M * N = closure (M * N) := by
  rw [← closure_mul_closure, closure_eq, closure_eq]

@[simp]
theorem mul_bot (S : AddSubmonoid R) : S * ⊥ = ⊥ :=
  eq_bot_iff.2 <|
    mul_le.2 fun m hm n hn => by
      rw [AddSubmonoid.mem_bot] at hn⊢ <;> rw [hn, mul_zero]

@[simp]
theorem bot_mul (S : AddSubmonoid R) : ⊥ * S = ⊥ :=
  eq_bot_iff.2 <|
    mul_le.2 fun m hm n hn => by
      rw [AddSubmonoid.mem_bot] at hm⊢ <;> rw [hm, zero_mul]

@[mono]
theorem mul_le_mul {M N P Q : AddSubmonoid R} (hmp : M ≤ P) (hnq : N ≤ Q) : M * N ≤ P * Q :=
  mul_le.2 fun m hm n hn => mul_mem_mul (hmp hm) (hnq hn)

theorem mul_le_mul_left {M N P : AddSubmonoid R} (h : M ≤ N) : M * P ≤ N * P :=
  mul_le_mul h (le_reflₓ P)

theorem mul_le_mul_right {M N P : AddSubmonoid R} (h : N ≤ P) : M * N ≤ M * P :=
  mul_le_mul (le_reflₓ M) h

theorem mul_subset_mul {M N : AddSubmonoid R} : (↑M : Set R) * (↑N : Set R) ⊆ (↑(M * N) : Set R) := by
  rintro _ ⟨i, j, hi, hj, rfl⟩
  exact mul_mem_mul hi hj

end NonUnitalNonAssocSemiringₓ

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing R]

/-- `add_submonoid.has_pointwise_neg` distributes over multiplication.

This is available as an instance in the `pointwise` locale. -/
protected def hasDistribNeg : HasDistribNeg (AddSubmonoid R) :=
  { AddSubmonoid.hasInvolutiveNeg with neg := Neg.neg,
    neg_mul := fun x y => by
      refine'
          le_antisymmₓ (mul_le.2 fun m hm n hn => _) ((AddSubmonoid.neg_le _ _).2 <| mul_le.2 fun m hm n hn => _) <;>
        simp only [← AddSubmonoid.mem_neg, neg_mul] at *
      · exact mul_mem_mul hm hn
        
      · exact mul_mem_mul (neg_mem_neg.2 hm) hn
        ,
    mul_neg := fun x y => by
      refine'
          le_antisymmₓ (mul_le.2 fun m hm n hn => _) ((AddSubmonoid.neg_le _ _).2 <| mul_le.2 fun m hm n hn => _) <;>
        simp only [← AddSubmonoid.mem_neg, mul_neg] at *
      · exact mul_mem_mul hm hn
        
      · exact mul_mem_mul hm (neg_mem_neg.2 hn)
         }

localized [Pointwise] attribute [instance] AddSubmonoid.hasDistribNeg

end NonUnitalNonAssocRing

section NonAssocSemiringₓ

variable [NonAssocSemiringₓ R]

instance : MulOneClassₓ (AddSubmonoid R) where
  one := 1
  mul := (· * ·)
  one_mul := fun M => by
    rw [one_eq_closure_one_set, ← closure_eq M, closure_mul_closure, one_mulₓ]
  mul_one := fun M => by
    rw [one_eq_closure_one_set, ← closure_eq M, closure_mul_closure, mul_oneₓ]

end NonAssocSemiringₓ

section NonUnitalSemiringₓ

variable [NonUnitalSemiringₓ R]

instance : Semigroupₓ (AddSubmonoid R) where
  mul := (· * ·)
  mul_assoc := fun M N P =>
    le_antisymmₓ
      (mul_le.2 fun mn hmn p hp =>
        suffices M * N ≤ (M * (N * P)).comap (AddMonoidHom.mulRight p) from this hmn
        mul_le.2 fun m hm n hn =>
          show m * n * p ∈ M * (N * P) from (mul_assoc m n p).symm ▸ mul_mem_mul hm (mul_mem_mul hn hp))
      (mul_le.2 fun m hm np hnp =>
        suffices N * P ≤ (M * N * P).comap (AddMonoidHom.mulLeft m) from this hnp
        mul_le.2 fun n hn p hp =>
          show m * (n * p) ∈ M * N * P from mul_assoc m n p ▸ mul_mem_mul (mul_mem_mul hm hn) hp)

end NonUnitalSemiringₓ

section Semiringₓ

variable [Semiringₓ R]

instance : Monoidₓ (AddSubmonoid R) :=
  { AddSubmonoid.semigroup, AddSubmonoid.mulOneClass with one := 1, mul := (· * ·) }

theorem closure_pow (s : Set R) : ∀ n : ℕ, closure s ^ n = closure (s ^ n)
  | 0 => by
    rw [pow_zeroₓ, pow_zeroₓ, one_eq_closure_one_set]
  | n + 1 => by
    rw [pow_succₓ, pow_succₓ, closure_pow, closure_mul_closure]

theorem pow_eq_closure_pow_set (s : AddSubmonoid R) (n : ℕ) : s ^ n = closure ((s : Set R) ^ n) := by
  rw [← closure_pow, closure_eq]

theorem pow_subset_pow {s : AddSubmonoid R} {n : ℕ} : (↑s : Set R) ^ n ⊆ ↑(s ^ n) :=
  (pow_eq_closure_pow_set s n).symm ▸ subset_closure

end Semiringₓ

end AddSubmonoid

