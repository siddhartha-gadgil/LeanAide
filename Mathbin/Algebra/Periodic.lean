/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
import Mathbin.Algebra.Field.Opposite
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.Order.Archimedean
import Mathbin.Data.Int.Parity
import Mathbin.GroupTheory.Coset

/-!
# Periodicity

In this file we define and then prove facts about periodic and antiperiodic functions.

## Main definitions

* `function.periodic`: A function `f` is *periodic* if `∀ x, f (x + c) = f x`.
  `f` is referred to as periodic with period `c` or `c`-periodic.

* `function.antiperiodic`: A function `f` is *antiperiodic* if `∀ x, f (x + c) = -f x`.
  `f` is referred to as antiperiodic with antiperiod `c` or `c`-antiperiodic.

Note that any `c`-antiperiodic function will necessarily also be `2*c`-periodic.

## Tags

period, periodic, periodicity, antiperiodic
-/


variable {α β γ : Type _} {f g : α → β} {c c₁ c₂ x : α}

open BigOperators

namespace Function

/-! ### Periodicity -/


/-- A function `f` is said to be `periodic` with period `c` if for all `x`, `f (x + c) = f x`. -/
@[simp]
def Periodic [Add α] (f : α → β) (c : α) : Prop :=
  ∀ x : α, f (x + c) = f x

theorem Periodic.funext [Add α] (h : Periodic f c) : (fun x => f (x + c)) = f :=
  funext h

theorem Periodic.comp [Add α] (h : Periodic f c) (g : β → γ) : Periodic (g ∘ f) c := by
  simp_all

theorem Periodic.comp_add_hom [Add α] [Add γ] (h : Periodic f c) (g : AddHom γ α) (g_inv : α → γ)
    (hg : RightInverse g_inv g) : Periodic (f ∘ g) (g_inv c) := fun x => by
  simp only [← hg c, ← h (g x), ← AddHom.map_add, ← comp_app]

@[to_additive]
theorem Periodic.mul [Add α] [Mul β] (hf : Periodic f c) (hg : Periodic g c) : Periodic (f * g) c := by
  simp_all

@[to_additive]
theorem Periodic.div [Add α] [Div β] (hf : Periodic f c) (hg : Periodic g c) : Periodic (f / g) c := by
  simp_all

@[to_additive]
theorem _root_.list.periodic_prod [Add α] [CommMonoidₓ β] (l : List (α → β)) (hl : ∀, ∀ f ∈ l, ∀, Periodic f c) :
    Periodic l.Prod c := by
  induction' l with g l ih hl
  · simp
    
  · simp only [← List.mem_cons_iff, ← forall_eq_or_imp] at hl
    obtain ⟨hg, hl⟩ := hl
    simp only [← List.prod_cons]
    exact hg.mul (ih hl)
    

@[to_additive]
theorem _root_.multiset.periodic_prod [Add α] [CommMonoidₓ β] (s : Multiset (α → β))
    (hs : ∀, ∀ f ∈ s, ∀, Periodic f c) : Periodic s.Prod c :=
  (s.prod_to_list ▸ s.toList.periodic_prod) fun f hf => hs f <| (Multiset.mem_to_list f s).mp hf

@[to_additive]
theorem _root_.finset.periodic_prod [Add α] [CommMonoidₓ β] {ι : Type _} {f : ι → α → β} (s : Finset ι)
    (hs : ∀, ∀ i ∈ s, ∀, Periodic (f i) c) : Periodic (∏ i in s, f i) c :=
  s.prod_to_list f ▸
    (s.toList.map f).periodic_prod
      (by
        simpa [-periodic] )

@[to_additive]
theorem Periodic.smul [Add α] [HasSmul γ β] (h : Periodic f c) (a : γ) : Periodic (a • f) c := by
  simp_all

theorem Periodic.const_smul [AddMonoidₓ α] [Groupₓ γ] [DistribMulAction γ α] (h : Periodic f c) (a : γ) :
    Periodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  simpa only [← smul_add, ← smul_inv_smul] using h (a • x)

theorem Periodic.const_smul₀ [AddCommMonoidₓ α] [DivisionRing γ] [Module γ α] (h : Periodic f c) (a : γ) :
    Periodic (fun x => f (a • x)) (a⁻¹ • c) := by
  intro x
  by_cases' ha : a = 0
  · simp only [← ha, ← zero_smul]
    
  simpa only [← smul_add, ← smul_inv_smul₀ ha] using h (a • x)

theorem Periodic.const_mul [DivisionRing α] (h : Periodic f c) (a : α) : Periodic (fun x => f (a * x)) (a⁻¹ * c) :=
  h.const_smul₀ a

theorem Periodic.const_inv_smul [AddMonoidₓ α] [Groupₓ γ] [DistribMulAction γ α] (h : Periodic f c) (a : γ) :
    Periodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [← inv_invₓ] using h.const_smul a⁻¹

theorem Periodic.const_inv_smul₀ [AddCommMonoidₓ α] [DivisionRing γ] [Module γ α] (h : Periodic f c) (a : γ) :
    Periodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [← inv_invₓ] using h.const_smul₀ a⁻¹

theorem Periodic.const_inv_mul [DivisionRing α] (h : Periodic f c) (a : α) : Periodic (fun x => f (a⁻¹ * x)) (a * c) :=
  h.const_inv_smul₀ a

theorem Periodic.mul_const [DivisionRing α] (h : Periodic f c) (a : α) : Periodic (fun x => f (x * a)) (c * a⁻¹) :=
  h.const_smul₀ <| MulOpposite.op a

theorem Periodic.mul_const' [DivisionRing α] (h : Periodic f c) (a : α) : Periodic (fun x => f (x * a)) (c / a) := by
  simpa only [← div_eq_mul_inv] using h.mul_const a

theorem Periodic.mul_const_inv [DivisionRing α] (h : Periodic f c) (a : α) : Periodic (fun x => f (x * a⁻¹)) (c * a) :=
  h.const_inv_smul₀ <| MulOpposite.op a

theorem Periodic.div_const [DivisionRing α] (h : Periodic f c) (a : α) : Periodic (fun x => f (x / a)) (c * a) := by
  simpa only [← div_eq_mul_inv] using h.mul_const_inv a

theorem Periodic.add_period [AddSemigroupₓ α] (h1 : Periodic f c₁) (h2 : Periodic f c₂) : Periodic f (c₁ + c₂) := by
  simp_all [add_assocₓ]

theorem Periodic.sub_eq [AddGroupₓ α] (h : Periodic f c) (x : α) : f (x - c) = f x := by
  simpa only [← sub_add_cancel] using (h (x - c)).symm

theorem Periodic.sub_eq' [AddCommGroupₓ α] (h : Periodic f c) : f (c - x) = f (-x) := by
  simpa only [← sub_eq_neg_add] using h (-x)

theorem Periodic.neg [AddGroupₓ α] (h : Periodic f c) : Periodic f (-c) := by
  simpa only [← sub_eq_add_neg, ← periodic] using h.sub_eq

theorem Periodic.sub_period [AddCommGroupₓ α] (h1 : Periodic f c₁) (h2 : Periodic f c₂) : Periodic f (c₁ - c₂) := by
  let h := h2.neg
  simp_all [← sub_eq_add_neg, ← add_commₓ c₁, add_assocₓ]

theorem Periodic.nsmul [AddMonoidₓ α] (h : Periodic f c) (n : ℕ) : Periodic f (n • c) := by
  induction n <;> simp_all [← Nat.succ_eq_add_one, ← add_nsmul, add_assocₓ, ← zero_nsmul]

theorem Periodic.nat_mul [Semiringₓ α] (h : Periodic f c) (n : ℕ) : Periodic f (n * c) := by
  simpa only [← nsmul_eq_mul] using h.nsmul n

theorem Periodic.neg_nsmul [AddGroupₓ α] (h : Periodic f c) (n : ℕ) : Periodic f (-(n • c)) :=
  (h.nsmul n).neg

theorem Periodic.neg_nat_mul [Ringₓ α] (h : Periodic f c) (n : ℕ) : Periodic f (-(n * c)) :=
  (h.nat_mul n).neg

theorem Periodic.sub_nsmul_eq [AddGroupₓ α] (h : Periodic f c) (n : ℕ) : f (x - n • c) = f x := by
  simpa only [← sub_eq_add_neg] using h.neg_nsmul n x

theorem Periodic.sub_nat_mul_eq [Ringₓ α] (h : Periodic f c) (n : ℕ) : f (x - n * c) = f x := by
  simpa only [← nsmul_eq_mul] using h.sub_nsmul_eq n

theorem Periodic.nsmul_sub_eq [AddCommGroupₓ α] (h : Periodic f c) (n : ℕ) : f (n • c - x) = f (-x) := by
  simpa only [← sub_eq_neg_add] using h.nsmul n (-x)

theorem Periodic.nat_mul_sub_eq [Ringₓ α] (h : Periodic f c) (n : ℕ) : f (n * c - x) = f (-x) := by
  simpa only [← sub_eq_neg_add] using h.nat_mul n (-x)

theorem Periodic.zsmul [AddGroupₓ α] (h : Periodic f c) (n : ℤ) : Periodic f (n • c) := by
  cases n
  · simpa only [← Int.of_nat_eq_coe, ← coe_nat_zsmul] using h.nsmul n
    
  · simpa only [← zsmul_neg_succ_of_nat] using (h.nsmul n.succ).neg
    

theorem Periodic.int_mul [Ringₓ α] (h : Periodic f c) (n : ℤ) : Periodic f (n * c) := by
  simpa only [← zsmul_eq_mul] using h.zsmul n

theorem Periodic.sub_zsmul_eq [AddGroupₓ α] (h : Periodic f c) (n : ℤ) : f (x - n • c) = f x :=
  (h.zsmul n).sub_eq x

theorem Periodic.sub_int_mul_eq [Ringₓ α] (h : Periodic f c) (n : ℤ) : f (x - n * c) = f x :=
  (h.int_mul n).sub_eq x

theorem Periodic.zsmul_sub_eq [AddCommGroupₓ α] (h : Periodic f c) (n : ℤ) : f (n • c - x) = f (-x) := by
  simpa only [← sub_eq_neg_add] using h.zsmul n (-x)

theorem Periodic.int_mul_sub_eq [Ringₓ α] (h : Periodic f c) (n : ℤ) : f (n * c - x) = f (-x) := by
  simpa only [← sub_eq_neg_add] using h.int_mul n (-x)

theorem Periodic.eq [AddZeroClassₓ α] (h : Periodic f c) : f c = f 0 := by
  simpa only [← zero_addₓ] using h 0

theorem Periodic.neg_eq [AddGroupₓ α] (h : Periodic f c) : f (-c) = f 0 :=
  h.neg.Eq

theorem Periodic.nsmul_eq [AddMonoidₓ α] (h : Periodic f c) (n : ℕ) : f (n • c) = f 0 :=
  (h.nsmul n).Eq

theorem Periodic.nat_mul_eq [Semiringₓ α] (h : Periodic f c) (n : ℕ) : f (n * c) = f 0 :=
  (h.nat_mul n).Eq

theorem Periodic.zsmul_eq [AddGroupₓ α] (h : Periodic f c) (n : ℤ) : f (n • c) = f 0 :=
  (h.zsmul n).Eq

theorem Periodic.int_mul_eq [Ringₓ α] (h : Periodic f c) (n : ℤ) : f (n * c) = f 0 :=
  (h.int_mul n).Eq

/-- If a function `f` is `periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ico 0 c` such that `f x = f y`. -/
theorem Periodic.exists_mem_Ico₀ [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c) (hc : 0 < c) (x) :
    ∃ y ∈ Set.Ico 0 c, f x = f y :=
  let ⟨n, H, _⟩ := exists_unique_zsmul_near_of_pos' hc x
  ⟨x - n • c, H, (h.sub_zsmul_eq n).symm⟩

/-- If a function `f` is `periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ico a (a + c)` such that `f x = f y`. -/
theorem Periodic.exists_mem_Ico [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c) (hc : 0 < c) (x a) :
    ∃ y ∈ Set.Ico a (a + c), f x = f y :=
  let ⟨n, H, _⟩ := exists_unique_add_zsmul_mem_Ico hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩

/-- If a function `f` is `periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ioc a (a + c)` such that `f x = f y`. -/
theorem Periodic.exists_mem_Ioc [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c) (hc : 0 < c) (x a) :
    ∃ y ∈ Set.Ioc a (a + c), f x = f y :=
  let ⟨n, H, _⟩ := exists_unique_add_zsmul_mem_Ioc hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩

theorem Periodic.image_Ioc [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c) (hc : 0 < c) (a : α) :
    f '' Set.Ioc a (a + c) = Set.Range f :=
  (Set.image_subset_range _ _).antisymm <|
    Set.range_subset_iff.2 fun x =>
      let ⟨y, hy, hyx⟩ := h.exists_mem_Ioc hc x a
      ⟨y, hy, hyx.symm⟩

theorem periodic_with_period_zero [AddZeroClassₓ α] (f : α → β) : Periodic f 0 := fun x => by
  rw [add_zeroₓ]

theorem Periodic.map_vadd_zmultiples [AddCommGroupₓ α] (hf : Periodic f c) (a : AddSubgroup.zmultiples c) (x : α) :
    f (a +ᵥ x) = f x := by
  rcases a with ⟨_, m, rfl⟩
  simp [← AddSubgroup.vadd_def, ← add_commₓ _ x, ← hf.zsmul m x]

theorem Periodic.map_vadd_multiples [AddCommMonoidₓ α] (hf : Periodic f c) (a : AddSubmonoid.multiples c) (x : α) :
    f (a +ᵥ x) = f x := by
  rcases a with ⟨_, m, rfl⟩
  simp [← AddSubmonoid.vadd_def, ← add_commₓ _ x, ← hf.nsmul m x]

/-- Lift a periodic function to a function from the quotient group. -/
def Periodic.lift [AddGroupₓ α] (h : Periodic f c) (x : α ⧸ AddSubgroup.zmultiples c) : β :=
  (Quotientₓ.liftOn' x f) fun a b h' => by
    rw [QuotientAddGroup.left_rel_apply] at h'
    obtain ⟨k, hk⟩ := h'
    exact (h.zsmul k _).symm.trans (congr_arg f (add_eq_of_eq_neg_add hk))

@[simp]
theorem Periodic.lift_coe [AddGroupₓ α] (h : Periodic f c) (a : α) : h.lift (a : α ⧸ AddSubgroup.zmultiples c) = f a :=
  rfl

/-! ### Antiperiodicity -/


/-- A function `f` is said to be `antiperiodic` with antiperiod `c` if for all `x`,
  `f (x + c) = -f x`. -/
@[simp]
def Antiperiodic [Add α] [Neg β] (f : α → β) (c : α) : Prop :=
  ∀ x : α, f (x + c) = -f x

theorem Antiperiodic.funext [Add α] [Neg β] (h : Antiperiodic f c) : (fun x => f (x + c)) = -f :=
  funext h

theorem Antiperiodic.funext' [Add α] [AddGroupₓ β] (h : Antiperiodic f c) : (fun x => -f (x + c)) = f :=
  (eq_neg_iff_eq_neg.mp h.funext).symm

/-- If a function is `antiperiodic` with antiperiod `c`, then it is also `periodic` with period
  `2 * c`. -/
theorem Antiperiodic.periodic [Semiringₓ α] [AddGroupₓ β] (h : Antiperiodic f c) : Periodic f (2 * c) := by
  simp [← two_mul, add_assocₓ, ← h _]

theorem Antiperiodic.eq [AddZeroClassₓ α] [Neg β] (h : Antiperiodic f c) : f c = -f 0 := by
  simpa only [← zero_addₓ] using h 0

theorem Antiperiodic.nat_even_mul_periodic [Semiringₓ α] [AddGroupₓ β] (h : Antiperiodic f c) (n : ℕ) :
    Periodic f (n * (2 * c)) :=
  h.Periodic.nat_mul n

theorem Antiperiodic.nat_odd_mul_antiperiodic [Semiringₓ α] [AddGroupₓ β] (h : Antiperiodic f c) (n : ℕ) :
    Antiperiodic f (n * (2 * c) + c) := fun x => by
  rw [← add_assocₓ, h, h.periodic.nat_mul]

theorem Antiperiodic.int_even_mul_periodic [Ringₓ α] [AddGroupₓ β] (h : Antiperiodic f c) (n : ℤ) :
    Periodic f (n * (2 * c)) :=
  h.Periodic.int_mul n

theorem Antiperiodic.int_odd_mul_antiperiodic [Ringₓ α] [AddGroupₓ β] (h : Antiperiodic f c) (n : ℤ) :
    Antiperiodic f (n * (2 * c) + c) := fun x => by
  rw [← add_assocₓ, h, h.periodic.int_mul]

theorem Antiperiodic.nat_mul_eq_of_eq_zero [CommSemiringₓ α] [AddGroupₓ β] (h : Antiperiodic f c) (hi : f 0 = 0)
    (n : ℕ) : f (n * c) = 0 := by
  rcases Nat.even_or_odd n with (⟨k, rfl⟩ | ⟨k, rfl⟩) <;>
    have hk : (k : α) * (2 * c) = 2 * k * c := by
      rw [mul_left_commₓ, ← mul_assoc]
  · simpa [two_mul, ← hk, ← hi] using (h.nat_even_mul_periodic k).Eq
    
  · simpa [← add_mulₓ, ← hk, ← hi] using (h.nat_odd_mul_antiperiodic k).Eq
    

theorem Antiperiodic.int_mul_eq_of_eq_zero [CommRingₓ α] [AddGroupₓ β] (h : Antiperiodic f c) (hi : f 0 = 0) (n : ℤ) :
    f (n * c) = 0 := by
  rcases Int.even_or_odd n with (⟨k, rfl⟩ | ⟨k, rfl⟩) <;>
    have hk : (k : α) * (2 * c) = 2 * k * c := by
      rw [mul_left_commₓ, ← mul_assoc]
  · simpa [two_mul, ← hk, ← hi] using (h.int_even_mul_periodic k).Eq
    
  · simpa [← add_mulₓ, ← hk, ← hi] using (h.int_odd_mul_antiperiodic k).Eq
    

theorem Antiperiodic.sub_eq [AddGroupₓ α] [AddGroupₓ β] (h : Antiperiodic f c) (x : α) : f (x - c) = -f x := by
  simp only [← eq_neg_iff_eq_neg.mp (h (x - c)), ← sub_add_cancel]

theorem Antiperiodic.sub_eq' [AddCommGroupₓ α] [AddGroupₓ β] (h : Antiperiodic f c) : f (c - x) = -f (-x) := by
  simpa only [← sub_eq_neg_add] using h (-x)

theorem Antiperiodic.neg [AddGroupₓ α] [AddGroupₓ β] (h : Antiperiodic f c) : Antiperiodic f (-c) := by
  simpa only [← sub_eq_add_neg, ← antiperiodic] using h.sub_eq

theorem Antiperiodic.neg_eq [AddGroupₓ α] [AddGroupₓ β] (h : Antiperiodic f c) : f (-c) = -f 0 := by
  simpa only [← zero_addₓ] using h.neg 0

theorem Antiperiodic.smul [Add α] [Monoidₓ γ] [AddGroupₓ β] [DistribMulAction γ β] (h : Antiperiodic f c) (a : γ) :
    Antiperiodic (a • f) c := by
  simp_all

theorem Antiperiodic.const_smul [AddMonoidₓ α] [Neg β] [Groupₓ γ] [DistribMulAction γ α] (h : Antiperiodic f c)
    (a : γ) : Antiperiodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  simpa only [← smul_add, ← smul_inv_smul] using h (a • x)

theorem Antiperiodic.const_smul₀ [AddCommMonoidₓ α] [Neg β] [DivisionRing γ] [Module γ α] (h : Antiperiodic f c) {a : γ}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  simpa only [← smul_add, ← smul_inv_smul₀ ha] using h (a • x)

theorem Antiperiodic.const_mul [DivisionRing α] [Neg β] (h : Antiperiodic f c) {a : α} (ha : a ≠ 0) :
    Antiperiodic (fun x => f (a * x)) (a⁻¹ * c) :=
  h.const_smul₀ ha

theorem Antiperiodic.const_inv_smul [AddMonoidₓ α] [Neg β] [Groupₓ γ] [DistribMulAction γ α] (h : Antiperiodic f c)
    (a : γ) : Antiperiodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [← inv_invₓ] using h.const_smul a⁻¹

theorem Antiperiodic.const_inv_smul₀ [AddCommMonoidₓ α] [Neg β] [DivisionRing γ] [Module γ α] (h : Antiperiodic f c)
    {a : γ} (ha : a ≠ 0) : Antiperiodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [← inv_invₓ] using h.const_smul₀ (inv_ne_zero ha)

theorem Antiperiodic.const_inv_mul [DivisionRing α] [Neg β] (h : Antiperiodic f c) {a : α} (ha : a ≠ 0) :
    Antiperiodic (fun x => f (a⁻¹ * x)) (a * c) :=
  h.const_inv_smul₀ ha

theorem Antiperiodic.mul_const [DivisionRing α] [Neg β] (h : Antiperiodic f c) {a : α} (ha : a ≠ 0) :
    Antiperiodic (fun x => f (x * a)) (c * a⁻¹) :=
  h.const_smul₀ <| (MulOpposite.op_ne_zero_iff a).mpr ha

theorem Antiperiodic.mul_const' [DivisionRing α] [Neg β] (h : Antiperiodic f c) {a : α} (ha : a ≠ 0) :
    Antiperiodic (fun x => f (x * a)) (c / a) := by
  simpa only [← div_eq_mul_inv] using h.mul_const ha

theorem Antiperiodic.mul_const_inv [DivisionRing α] [Neg β] (h : Antiperiodic f c) {a : α} (ha : a ≠ 0) :
    Antiperiodic (fun x => f (x * a⁻¹)) (c * a) :=
  h.const_inv_smul₀ <| (MulOpposite.op_ne_zero_iff a).mpr ha

theorem Antiperiodic.div_inv [DivisionRing α] [Neg β] (h : Antiperiodic f c) {a : α} (ha : a ≠ 0) :
    Antiperiodic (fun x => f (x / a)) (c * a) := by
  simpa only [← div_eq_mul_inv] using h.mul_const_inv ha

theorem Antiperiodic.add [AddGroupₓ α] [AddGroupₓ β] (h1 : Antiperiodic f c₁) (h2 : Antiperiodic f c₂) :
    Periodic f (c₁ + c₂) := by
  simp_all [add_assocₓ]

theorem Antiperiodic.sub [AddCommGroupₓ α] [AddGroupₓ β] (h1 : Antiperiodic f c₁) (h2 : Antiperiodic f c₂) :
    Periodic f (c₁ - c₂) := by
  let h := h2.neg
  simp_all [← sub_eq_add_neg, ← add_commₓ c₁, add_assocₓ]

theorem Periodic.add_antiperiod [AddGroupₓ α] [AddGroupₓ β] (h1 : Periodic f c₁) (h2 : Antiperiodic f c₂) :
    Antiperiodic f (c₁ + c₂) := by
  simp_all [add_assocₓ]

theorem Periodic.sub_antiperiod [AddCommGroupₓ α] [AddGroupₓ β] (h1 : Periodic f c₁) (h2 : Antiperiodic f c₂) :
    Antiperiodic f (c₁ - c₂) := by
  let h := h2.neg
  simp_all [← sub_eq_add_neg, ← add_commₓ c₁, add_assocₓ]

theorem Periodic.add_antiperiod_eq [AddGroupₓ α] [AddGroupₓ β] (h1 : Periodic f c₁) (h2 : Antiperiodic f c₂) :
    f (c₁ + c₂) = -f 0 :=
  (h1.add_antiperiod h2).Eq

theorem Periodic.sub_antiperiod_eq [AddCommGroupₓ α] [AddGroupₓ β] (h1 : Periodic f c₁) (h2 : Antiperiodic f c₂) :
    f (c₁ - c₂) = -f 0 :=
  (h1.sub_antiperiod h2).Eq

theorem Antiperiodic.mul [Add α] [Ringₓ β] (hf : Antiperiodic f c) (hg : Antiperiodic g c) : Periodic (f * g) c := by
  simp_all

theorem Antiperiodic.div [Add α] [DivisionRing β] (hf : Antiperiodic f c) (hg : Antiperiodic g c) :
    Periodic (f / g) c := by
  simp_all [← neg_div_neg_eq]

end Function

