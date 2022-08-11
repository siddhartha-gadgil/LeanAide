/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Julian Kuelshammer
-/
import Mathbin.Algebra.Hom.Iterate
import Mathbin.Data.Nat.Modeq
import Mathbin.Data.Set.Pointwise
import Mathbin.Dynamics.PeriodicPts
import Mathbin.GroupTheory.Index

/-!
# Order of an element

This file defines the order of an element of a finite group. For a finite group `G` the order of
`x ∈ G` is the minimal `n ≥ 1` such that `x ^ n = 1`.

## Main definitions

* `is_of_fin_order` is a predicate on an element `x` of a monoid `G` saying that `x` is of finite
  order.
* `is_of_fin_add_order` is the additive analogue of `is_of_fin_order`.
* `order_of x` defines the order of an element `x` of a monoid `G`, by convention its value is `0`
  if `x` has infinite order.
* `add_order_of` is the additive analogue of `order_of`.

## Tags
order of an element
-/


open Function Nat

open Pointwise

universe u v

variable {G : Type u} {A : Type v}

variable {x y : G} {a b : A} {n m : ℕ}

section MonoidAddMonoid

variable [Monoidₓ G] [AddMonoidₓ A]

section IsOfFinOrder

@[to_additive]
theorem is_periodic_pt_mul_iff_pow_eq_one (x : G) : IsPeriodicPt ((· * ·) x) n 1 ↔ x ^ n = 1 := by
  rw [is_periodic_pt, is_fixed_pt, mul_left_iterate, mul_oneₓ]

/-- `is_of_fin_add_order` is a predicate on an element `a` of an additive monoid to be of finite
order, i.e. there exists `n ≥ 1` such that `n • a = 0`.-/
def IsOfFinAddOrder (a : A) : Prop :=
  (0 : A) ∈ PeriodicPts ((· + ·) a)

/-- `is_of_fin_order` is a predicate on an element `x` of a monoid to be of finite order, i.e. there
exists `n ≥ 1` such that `x ^ n = 1`.-/
@[to_additive IsOfFinAddOrder]
def IsOfFinOrder (x : G) : Prop :=
  (1 : G) ∈ PeriodicPts ((· * ·) x)

theorem is_of_fin_add_order_of_mul_iff : IsOfFinAddOrder (Additive.ofMul x) ↔ IsOfFinOrder x :=
  Iff.rfl

theorem is_of_fin_order_of_add_iff : IsOfFinOrder (Multiplicative.ofAdd a) ↔ IsOfFinAddOrder a :=
  Iff.rfl

@[to_additive is_of_fin_add_order_iff_nsmul_eq_zero]
theorem is_of_fin_order_iff_pow_eq_one (x : G) : IsOfFinOrder x ↔ ∃ n, 0 < n ∧ x ^ n = 1 := by
  convert Iff.rfl
  simp [← is_periodic_pt_mul_iff_pow_eq_one]

/-- Elements of finite order are of finite order in submonoids.-/
@[to_additive is_of_fin_add_order_iff_coe]
theorem is_of_fin_order_iff_coe (H : Submonoid G) (x : H) : IsOfFinOrder x ↔ IsOfFinOrder (x : G) := by
  rw [is_of_fin_order_iff_pow_eq_one, is_of_fin_order_iff_pow_eq_one]
  norm_cast

/-- The image of an element of finite order has finite order. -/
@[to_additive AddMonoidHom.is_of_fin_order
      "The image of an element of finite additive order has finite additive order."]
theorem MonoidHom.is_of_fin_order {H : Type v} [Monoidₓ H] (f : G →* H) {x : G} (h : IsOfFinOrder x) :
    IsOfFinOrder <| f x :=
  (is_of_fin_order_iff_pow_eq_one _).mpr <| by
    rcases(is_of_fin_order_iff_pow_eq_one _).mp h with ⟨n, npos, hn⟩
    exact
      ⟨n, npos, by
        rw [← f.map_pow, hn, f.map_one]⟩

/-- If a direct product has finite order then so does each component. -/
@[to_additive "If a direct product has finite additive order then so does each component."]
theorem IsOfFinOrder.apply {η : Type _} {Gs : η → Type _} [∀ i, Monoidₓ (Gs i)] {x : ∀ i, Gs i} (h : IsOfFinOrder x) :
    ∀ i, IsOfFinOrder (x i) := by
  rcases(is_of_fin_order_iff_pow_eq_one _).mp h with ⟨n, npos, hn⟩
  exact fun _ => (is_of_fin_order_iff_pow_eq_one _).mpr ⟨n, npos, (congr_fun hn.symm _).symm⟩

/-- 1 is of finite order in any monoid. -/
@[to_additive "0 is of finite order in any additive monoid."]
theorem is_of_fin_order_one : IsOfFinOrder (1 : G) :=
  (is_of_fin_order_iff_pow_eq_one 1).mpr ⟨1, one_pos, one_pow 1⟩

end IsOfFinOrder

/-- `order_of x` is the order of the element `x`, i.e. the `n ≥ 1`, s.t. `x ^ n = 1` if it exists.
Otherwise, i.e. if `x` is of infinite order, then `order_of x` is `0` by convention.-/
@[to_additive addOrderOf
      "`add_order_of a` is the order of the element `a`, i.e. the `n ≥ 1`, s.t. `n • a = 0` if it\nexists. Otherwise, i.e. if `a` is of infinite order, then `add_order_of a` is `0` by convention."]
noncomputable def orderOf (x : G) : ℕ :=
  minimalPeriod ((· * ·) x) 1

@[simp]
theorem add_order_of_of_mul_eq_order_of (x : G) : addOrderOf (Additive.ofMul x) = orderOf x :=
  rfl

@[simp]
theorem order_of_of_add_eq_add_order_of (a : A) : orderOf (Multiplicative.ofAdd a) = addOrderOf a :=
  rfl

@[to_additive add_order_of_pos']
theorem order_of_pos' (h : IsOfFinOrder x) : 0 < orderOf x :=
  minimal_period_pos_of_mem_periodic_pts h

@[to_additive add_order_of_nsmul_eq_zero]
theorem pow_order_of_eq_one (x : G) : x ^ orderOf x = 1 := by
  convert is_periodic_pt_minimal_period ((· * ·) x) _
  rw [orderOf, mul_left_iterate, mul_oneₓ]

@[to_additive add_order_of_eq_zero]
theorem order_of_eq_zero (h : ¬IsOfFinOrder x) : orderOf x = 0 := by
  rwa [orderOf, minimal_period, dif_neg]

@[to_additive add_order_of_eq_zero_iff]
theorem order_of_eq_zero_iff : orderOf x = 0 ↔ ¬IsOfFinOrder x :=
  ⟨fun h H => (order_of_pos' H).ne' h, order_of_eq_zero⟩

@[to_additive add_order_of_eq_zero_iff']
theorem order_of_eq_zero_iff' : orderOf x = 0 ↔ ∀ n : ℕ, 0 < n → x ^ n ≠ 1 := by
  simp_rw [order_of_eq_zero_iff, is_of_fin_order_iff_pow_eq_one, not_exists, not_and]

/-- A group element has finite order iff its order is positive. -/
@[to_additive add_order_of_pos_iff "A group element has finite additive order iff its order is positive."]
theorem order_of_pos_iff : 0 < orderOf x ↔ IsOfFinOrder x := by
  rwa [iff_not_comm.mp order_of_eq_zero_iff, pos_iff_ne_zero]

@[to_additive nsmul_ne_zero_of_lt_add_order_of']
theorem pow_ne_one_of_lt_order_of' (n0 : n ≠ 0) (h : n < orderOf x) : x ^ n ≠ 1 := fun j =>
  not_is_periodic_pt_of_pos_of_lt_minimal_period n0 h ((is_periodic_pt_mul_iff_pow_eq_one x).mpr j)

@[to_additive add_order_of_le_of_nsmul_eq_zero]
theorem order_of_le_of_pow_eq_one (hn : 0 < n) (h : x ^ n = 1) : orderOf x ≤ n :=
  IsPeriodicPt.minimal_period_le hn
    (by
      rwa [is_periodic_pt_mul_iff_pow_eq_one])

@[simp, to_additive]
theorem order_of_one : orderOf (1 : G) = 1 := by
  rw [orderOf, one_mul_eq_id, minimal_period_id]

@[simp, to_additive AddMonoidₓ.order_of_eq_one_iff]
theorem order_of_eq_one_iff : orderOf x = 1 ↔ x = 1 := by
  rw [orderOf, is_fixed_point_iff_minimal_period_eq_one, is_fixed_pt, mul_oneₓ]

@[to_additive nsmul_eq_mod_add_order_of]
theorem pow_eq_mod_order_of {n : ℕ} : x ^ n = x ^ (n % orderOf x) :=
  calc
    x ^ n = x ^ (n % orderOf x + orderOf x * (n / orderOf x)) := by
      rw [Nat.mod_add_divₓ]
    _ = x ^ (n % orderOf x) := by
      simp [← pow_addₓ, ← pow_mulₓ, ← pow_order_of_eq_one]
    

@[to_additive add_order_of_dvd_of_nsmul_eq_zero]
theorem order_of_dvd_of_pow_eq_one (h : x ^ n = 1) : orderOf x ∣ n :=
  IsPeriodicPt.minimal_period_dvd ((is_periodic_pt_mul_iff_pow_eq_one _).mpr h)

@[to_additive add_order_of_dvd_iff_nsmul_eq_zero]
theorem order_of_dvd_iff_pow_eq_one {n : ℕ} : orderOf x ∣ n ↔ x ^ n = 1 :=
  ⟨fun h => by
    rw [pow_eq_mod_order_of, Nat.mod_eq_zero_of_dvdₓ h, pow_zeroₓ], order_of_dvd_of_pow_eq_one⟩

@[to_additive add_order_of_map_dvd]
theorem order_of_map_dvd {H : Type _} [Monoidₓ H] (ψ : G →* H) (x : G) : orderOf (ψ x) ∣ orderOf x := by
  apply order_of_dvd_of_pow_eq_one
  rw [← map_pow, pow_order_of_eq_one]
  apply map_one

@[to_additive]
theorem exists_pow_eq_self_of_coprime (h : n.Coprime (orderOf x)) : ∃ m : ℕ, (x ^ n) ^ m = x := by
  by_cases' h0 : orderOf x = 0
  · rw [h0, coprime_zero_right] at h
    exact
      ⟨1, by
        rw [h, pow_oneₓ, pow_oneₓ]⟩
    
  by_cases' h1 : orderOf x = 1
  · exact
      ⟨0, by
        rw [order_of_eq_one_iff.mp h1, one_pow, one_pow]⟩
    
  obtain ⟨m, hm⟩ := exists_mul_mod_eq_one_of_coprime h (one_lt_iff_ne_zero_and_ne_one.mpr ⟨h0, h1⟩)
  exact
    ⟨m, by
      rw [← pow_mulₓ, pow_eq_mod_order_of, hm, pow_oneₓ]⟩

/-- If `x^n = 1`, but `x^(n/p) ≠ 1` for all prime factors `p` of `r`,
then `x` has order `n` in `G`.
-/
@[to_additive add_order_of_eq_of_nsmul_and_div_prime_nsmul]
theorem order_of_eq_of_pow_and_pow_div_prime (hn : 0 < n) (hx : x ^ n = 1)
    (hd : ∀ p : ℕ, p.Prime → p ∣ n → x ^ (n / p) ≠ 1) : orderOf x = n := by
  -- Let `a` be `n/(order_of x)`, and show `a = 1`
  cases' exists_eq_mul_right_of_dvd (order_of_dvd_of_pow_eq_one hx) with a ha
  suffices a = 1 by
    simp [← this, ← ha]
  -- Assume `a` is not one...
  by_contra
  have a_min_fac_dvd_p_sub_one : a.min_fac ∣ n := by
    obtain ⟨b, hb⟩ : ∃ b : ℕ, a = b * a.min_fac := exists_eq_mul_left_of_dvd a.min_fac_dvd
    rw [hb, ← mul_assoc] at ha
    exact Dvd.intro_left (orderOf x * b) ha.symm
  -- Use the minimum prime factor of `a` as `p`.
  refine' hd a.min_fac (Nat.min_fac_prime h) a_min_fac_dvd_p_sub_one _
  rw [← order_of_dvd_iff_pow_eq_one, Nat.dvd_div_iff a_min_fac_dvd_p_sub_one, ha, mul_comm,
    Nat.mul_dvd_mul_iff_left (order_of_pos' _)]
  · exact Nat.min_fac_dvd a
    
  · rw [is_of_fin_order_iff_pow_eq_one]
    exact Exists.intro n (id ⟨hn, hx⟩)
    

@[to_additive add_order_of_eq_add_order_of_iff]
theorem order_of_eq_order_of_iff {H : Type _} [Monoidₓ H] {y : H} :
    orderOf x = orderOf y ↔ ∀ n : ℕ, x ^ n = 1 ↔ y ^ n = 1 := by
  simp_rw [← is_periodic_pt_mul_iff_pow_eq_one, ← minimal_period_eq_minimal_period_iff, orderOf]

@[to_additive add_order_of_injective]
theorem order_of_injective {H : Type _} [Monoidₓ H] (f : G →* H) (hf : Function.Injective f) (x : G) :
    orderOf (f x) = orderOf x := by
  simp_rw [order_of_eq_order_of_iff, ← f.map_pow, ← f.map_one, hf.eq_iff, iff_selfₓ, forall_const]

@[simp, norm_cast, to_additive]
theorem order_of_submonoid {H : Submonoid G} (y : H) : orderOf (y : G) = orderOf y :=
  order_of_injective H.Subtype Subtype.coe_injective y

@[to_additive]
theorem order_of_units {y : Gˣ} : orderOf (y : G) = orderOf y :=
  order_of_injective (Units.coeHom G) Units.ext y

variable (x)

@[to_additive add_order_of_nsmul']
theorem order_of_pow' (h : n ≠ 0) : orderOf (x ^ n) = orderOf x / gcdₓ (orderOf x) n := by
  convert minimal_period_iterate_eq_div_gcd h
  simp only [← orderOf, ← mul_left_iterate]

variable (a) (n)

@[to_additive add_order_of_nsmul'']
theorem order_of_pow'' (h : IsOfFinOrder x) : orderOf (x ^ n) = orderOf x / gcdₓ (orderOf x) n := by
  convert minimal_period_iterate_eq_div_gcd' h
  simp only [← orderOf, ← mul_left_iterate]

@[to_additive]
theorem Commute.order_of_mul_dvd_lcm {x y : G} (h : Commute x y) : orderOf (x * y) ∣ Nat.lcmₓ (orderOf x) (orderOf y) :=
  by
  convert Function.Commute.minimal_period_of_comp_dvd_lcm h.function_commute_mul_left
  rw [orderOf, comp_mul_left]

@[to_additive add_order_of_add_dvd_mul_add_order_of]
theorem Commute.order_of_mul_dvd_mul_order_of {x y : G} (h : Commute x y) : orderOf (x * y) ∣ orderOf x * orderOf y :=
  dvd_trans h.order_of_mul_dvd_lcm (lcm_dvd_mul _ _)

@[to_additive add_order_of_add_eq_mul_add_order_of_of_coprime]
theorem Commute.order_of_mul_eq_mul_order_of_of_coprime {x y : G} (h : Commute x y)
    (hco : Nat.Coprime (orderOf x) (orderOf y)) : orderOf (x * y) = orderOf x * orderOf y := by
  convert h.function_commute_mul_left.minimal_period_of_comp_eq_mul_of_coprime hco
  simp only [← orderOf, ← comp_mul_left]

/-- Commuting elements of finite order are closed under multiplication. -/
@[to_additive "Commuting elements of finite additive order are closed under addition."]
theorem Commute.is_of_fin_order_mul {x} (h : Commute x y) (hx : IsOfFinOrder x) (hy : IsOfFinOrder y) :
    IsOfFinOrder (x * y) :=
  order_of_pos_iff.mp <|
    pos_of_dvd_of_posₓ h.order_of_mul_dvd_mul_order_of <| mul_pos (order_of_pos' hx) (order_of_pos' hy)

section PPrime

variable {a x n} {p : ℕ} [hp : Fact p.Prime]

include hp

@[to_additive add_order_of_eq_prime]
theorem order_of_eq_prime (hg : x ^ p = 1) (hg1 : x ≠ 1) : orderOf x = p :=
  minimal_period_eq_prime ((is_periodic_pt_mul_iff_pow_eq_one _).mpr hg)
    (by
      rwa [is_fixed_pt, mul_oneₓ])

@[to_additive add_order_of_eq_prime_pow]
theorem order_of_eq_prime_pow (hnot : ¬x ^ p ^ n = 1) (hfin : x ^ p ^ (n + 1) = 1) : orderOf x = p ^ (n + 1) := by
  apply minimal_period_eq_prime_pow <;> rwa [is_periodic_pt_mul_iff_pow_eq_one]

@[to_additive exists_add_order_of_eq_prime_pow_iff]
theorem exists_order_of_eq_prime_pow_iff : (∃ k : ℕ, orderOf x = p ^ k) ↔ ∃ m : ℕ, x ^ (p : ℕ) ^ m = 1 :=
  ⟨fun ⟨k, hk⟩ =>
    ⟨k, by
      rw [← hk, pow_order_of_eq_one]⟩,
    fun ⟨_, hm⟩ => by
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp.elim).mp (order_of_dvd_of_pow_eq_one hm)
    exact ⟨k, hk⟩⟩

omit hp

-- An example on how to determine the order of an element of a finite group.
example : orderOf (-1 : ℤˣ) = 2 :=
  order_of_eq_prime (Int.units_sq _)
    (by
      decide)

end PPrime

end MonoidAddMonoid

section CancelMonoid

variable [LeftCancelMonoid G] (x y)

@[to_additive nsmul_injective_of_lt_add_order_of]
theorem pow_injective_of_lt_order_of (hn : n < orderOf x) (hm : m < orderOf x) (eq : x ^ n = x ^ m) : n = m :=
  eq_of_lt_minimal_period_of_iterate_eq hn hm
    (by
      simpa only [← mul_left_iterate, ← mul_oneₓ] )

@[to_additive mem_multiples_iff_mem_range_add_order_of']
theorem mem_powers_iff_mem_range_order_of' [DecidableEq G] (hx : 0 < orderOf x) :
    y ∈ Submonoid.powers x ↔ y ∈ (Finset.range (orderOf x)).Image ((· ^ ·) x : ℕ → G) :=
  Finset.mem_range_iff_mem_finset_range_of_mod_eq' hx fun i => pow_eq_mod_order_of.symm

theorem pow_eq_one_iff_modeq : x ^ n = 1 ↔ n ≡ 0 [MOD orderOf x] := by
  rw [modeq_zero_iff_dvd, order_of_dvd_iff_pow_eq_one]

theorem pow_eq_pow_iff_modeq : x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x] := by
  wlog hmn : m ≤ n
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [← mul_oneₓ (x ^ m), pow_addₓ, mul_left_cancel_iffₓ, pow_eq_one_iff_modeq]
  exact ⟨fun h => Nat.Modeq.add_left _ h, fun h => Nat.Modeq.add_left_cancel' _ h⟩

end CancelMonoid

section Groupₓ

variable [Groupₓ G] [AddGroupₓ A] {x a} {i : ℤ}

/-- Inverses of elements of finite order have finite order. -/
@[to_additive "Inverses of elements of finite additive order have finite additive order."]
theorem IsOfFinOrder.inv {x : G} (hx : IsOfFinOrder x) : IsOfFinOrder x⁻¹ :=
  (is_of_fin_order_iff_pow_eq_one _).mpr <| by
    rcases(is_of_fin_order_iff_pow_eq_one x).mp hx with ⟨n, npos, hn⟩
    refine'
      ⟨n, npos, by
        simp_rw [inv_pow, hn, inv_one]⟩

/-- Inverses of elements of finite order have finite order. -/
@[simp, to_additive "Inverses of elements of finite additive order have finite additive order."]
theorem is_of_fin_order_inv_iff {x : G} : IsOfFinOrder x⁻¹ ↔ IsOfFinOrder x :=
  ⟨fun h => inv_invₓ x ▸ h.inv, IsOfFinOrder.inv⟩

@[to_additive add_order_of_dvd_iff_zsmul_eq_zero]
theorem order_of_dvd_iff_zpow_eq_one : (orderOf x : ℤ) ∣ i ↔ x ^ i = 1 := by
  rcases Int.eq_coe_or_neg i with ⟨i, rfl | rfl⟩
  · rw [Int.coe_nat_dvd, order_of_dvd_iff_pow_eq_one, zpow_coe_nat]
    
  · rw [dvd_neg, Int.coe_nat_dvd, zpow_neg, inv_eq_one, zpow_coe_nat, order_of_dvd_iff_pow_eq_one]
    

@[simp, to_additive]
theorem order_of_inv (x : G) : orderOf x⁻¹ = orderOf x := by
  simp [← order_of_eq_order_of_iff]

@[simp, norm_cast, to_additive]
theorem order_of_subgroup {H : Subgroup G} (y : H) : orderOf (y : G) = orderOf y :=
  order_of_injective H.Subtype Subtype.coe_injective y

@[to_additive zsmul_eq_mod_add_order_of]
theorem zpow_eq_mod_order_of : x ^ i = x ^ (i % orderOf x) :=
  calc
    x ^ i = x ^ (i % orderOf x + orderOf x * (i / orderOf x)) := by
      rw [Int.mod_add_div]
    _ = x ^ (i % orderOf x) := by
      simp [← zpow_add, ← zpow_mul, ← pow_order_of_eq_one]
    

@[to_additive nsmul_inj_iff_of_add_order_of_eq_zero]
theorem pow_inj_iff_of_order_of_eq_zero (h : orderOf x = 0) {n m : ℕ} : x ^ n = x ^ m ↔ n = m := by
  rw [order_of_eq_zero_iff, is_of_fin_order_iff_pow_eq_one] at h
  push_neg  at h
  induction' n with n IH generalizing m
  · cases m
    · simp
      
    · simpa [← eq_comm] using h m.succ m.zero_lt_succ
      
    
  · cases m
    · simpa using h n.succ n.zero_lt_succ
      
    · simp [← pow_succₓ, ← IH]
      
    

@[to_additive]
theorem pow_inj_mod {n m : ℕ} : x ^ n = x ^ m ↔ n % orderOf x = m % orderOf x := by
  cases' (orderOf x).zero_le.eq_or_lt with hx hx
  · simp [← pow_inj_iff_of_order_of_eq_zero, ← hx.symm]
    
  rw [pow_eq_mod_order_of, @pow_eq_mod_order_of _ _ _ m]
  exact ⟨pow_injective_of_lt_order_of _ (Nat.mod_ltₓ _ hx) (Nat.mod_ltₓ _ hx), fun h => congr_arg _ h⟩

end Groupₓ

section CommMonoidₓ

variable [CommMonoidₓ G]

/-- Elements of finite order are closed under multiplication. -/
@[to_additive "Elements of finite additive order are closed under addition."]
theorem IsOfFinOrder.mul (hx : IsOfFinOrder x) (hy : IsOfFinOrder y) : IsOfFinOrder (x * y) :=
  (Commute.all x y).is_of_fin_order_mul hx hy

end CommMonoidₓ

section Fintype

variable [Fintype G] [Fintype A]

section FiniteMonoid

variable [Monoidₓ G] [AddMonoidₓ A]

open BigOperators

@[to_additive sum_card_add_order_of_eq_card_nsmul_eq_zero]
theorem sum_card_order_of_eq_card_pow_eq_one [DecidableEq G] (hn : 0 < n) :
    (∑ m in (Finset.range n.succ).filter (· ∣ n), (Finset.univ.filter fun x : G => orderOf x = m).card) =
      (Finset.univ.filter fun x : G => x ^ n = 1).card :=
  calc
    (∑ m in (Finset.range n.succ).filter (· ∣ n), (Finset.univ.filter fun x : G => orderOf x = m).card) = _ :=
      (Finset.card_bUnion
          (by
            intros
            apply Finset.disjoint_filter.2
            cc)).symm
    _ = _ :=
      congr_arg Finset.card
        (Finset.ext
          (by
            intro x
            suffices orderOf x ≤ n ∧ orderOf x ∣ n ↔ x ^ n = 1 by
              simpa [← Nat.lt_succ_iffₓ]
            exact
              ⟨fun h => by
                let ⟨m, hm⟩ := h.2
                rw [hm, pow_mulₓ, pow_order_of_eq_one, one_pow], fun h =>
                ⟨order_of_le_of_pow_eq_one hn h, order_of_dvd_of_pow_eq_one h⟩⟩))
    

end FiniteMonoid

section FiniteCancelMonoid

-- TODO: Of course everything also works for right_cancel_monoids.
variable [LeftCancelMonoid G] [AddLeftCancelMonoid A]

-- TODO: Use this to show that a finite left cancellative monoid is a group.
@[to_additive]
theorem exists_pow_eq_one (x : G) : IsOfFinOrder x := by
  refine' (is_of_fin_order_iff_pow_eq_one _).mpr _
  obtain ⟨i, j, a_eq, ne⟩ : ∃ i j : ℕ, x ^ i = x ^ j ∧ i ≠ j := by
    simpa only [← not_forall, ← exists_prop, ← injective] using not_injective_infinite_fintype fun i : ℕ => x ^ i
  wlog h'' : j ≤ i
  refine' ⟨i - j, tsub_pos_of_lt (lt_of_le_of_neₓ h'' Ne.symm), mul_right_injective (x ^ j) _⟩
  rw [mul_oneₓ, ← pow_addₓ, ← a_eq, add_tsub_cancel_of_le h'']

@[to_additive add_order_of_le_card_univ]
theorem order_of_le_card_univ : orderOf x ≤ Fintype.card G :=
  Finset.le_card_of_inj_on_range ((· ^ ·) x) (fun n _ => Finset.mem_univ _) fun i hi j hj =>
    pow_injective_of_lt_order_of x hi hj

/-- This is the same as `order_of_pos' but with one fewer explicit assumption since this is
  automatic in case of a finite cancellative monoid.-/
@[to_additive add_order_of_pos
      "This is the same as `add_order_of_pos' but with one fewer explicit assumption since this is\n  automatic in case of a finite cancellative additive monoid."]
theorem order_of_pos (x : G) : 0 < orderOf x :=
  order_of_pos' (exists_pow_eq_one x)

open Nat

/-- This is the same as `order_of_pow'` and `order_of_pow''` but with one assumption less which is
automatic in the case of a finite cancellative monoid.-/
@[to_additive add_order_of_nsmul
      "This is the same as `add_order_of_nsmul'` and `add_order_of_nsmul` but with one assumption less\nwhich is automatic in the case of a finite cancellative additive monoid."]
theorem order_of_pow (x : G) : orderOf (x ^ n) = orderOf x / gcdₓ (orderOf x) n :=
  order_of_pow'' _ _ (exists_pow_eq_one _)

@[to_additive mem_multiples_iff_mem_range_add_order_of]
theorem mem_powers_iff_mem_range_order_of [DecidableEq G] :
    y ∈ Submonoid.powers x ↔ y ∈ (Finset.range (orderOf x)).Image ((· ^ ·) x : ℕ → G) :=
  Finset.mem_range_iff_mem_finset_range_of_mod_eq' (order_of_pos x) fun i => pow_eq_mod_order_of.symm

@[to_additive decidableMultiples]
noncomputable instance decidablePowers [DecidableEq G] : DecidablePred (· ∈ Submonoid.powers x) := by
  intro y
  apply decidableOfIff' (y ∈ (Finset.range (orderOf x)).Image ((· ^ ·) x))
  exact mem_powers_iff_mem_range_order_of

/-- The equivalence between `fin (order_of x)` and `submonoid.powers x`, sending `i` to `x ^ i`."-/
@[to_additive finEquivMultiples
      "The equivalence between `fin (add_order_of a)` and\n`add_submonoid.multiples a`, sending `i` to `i • a`."]
noncomputable def finEquivPowers (x : G) : Finₓ (orderOf x) ≃ (Submonoid.powers x : Set G) :=
  Equivₓ.ofBijective (fun n => ⟨x ^ ↑n, ⟨n, rfl⟩⟩)
    ⟨fun ⟨i, hi⟩ ⟨j, hj⟩ ij => Subtype.mk_eq_mk.2 (pow_injective_of_lt_order_of x hi hj (Subtype.mk_eq_mk.1 ij)),
      fun ⟨_, i, rfl⟩ => ⟨⟨i % orderOf x, mod_ltₓ i (order_of_pos x)⟩, Subtype.eq pow_eq_mod_order_of.symm⟩⟩

@[simp, to_additive fin_equiv_multiples_apply]
theorem fin_equiv_powers_apply {x : G} {n : Finₓ (orderOf x)} : finEquivPowers x n = ⟨x ^ ↑n, n, rfl⟩ :=
  rfl

@[simp, to_additive fin_equiv_multiples_symm_apply]
theorem fin_equiv_powers_symm_apply (x : G) (n : ℕ) {hn : ∃ m : ℕ, x ^ m = x ^ n} :
    (finEquivPowers x).symm ⟨x ^ n, hn⟩ = ⟨n % orderOf x, Nat.mod_ltₓ _ (order_of_pos x)⟩ := by
  rw [Equivₓ.symm_apply_eq, fin_equiv_powers_apply, Subtype.mk_eq_mk, pow_eq_mod_order_of, Finₓ.coe_mk]

/-- The equivalence between `submonoid.powers` of two elements `x, y` of the same order, mapping
  `x ^ i` to `y ^ i`. -/
@[to_additive multiplesEquivMultiples
      "The equivalence between `submonoid.multiples` of two elements `a, b` of the same additive order,\n  mapping `i • a` to `i • b`."]
noncomputable def powersEquivPowers (h : orderOf x = orderOf y) :
    (Submonoid.powers x : Set G) ≃ (Submonoid.powers y : Set G) :=
  (finEquivPowers x).symm.trans ((Finₓ.cast h).toEquiv.trans (finEquivPowers y))

@[simp, to_additive multiples_equiv_multiples_apply]
theorem powers_equiv_powers_apply (h : orderOf x = orderOf y) (n : ℕ) :
    powersEquivPowers h ⟨x ^ n, n, rfl⟩ = ⟨y ^ n, n, rfl⟩ := by
  rw [powersEquivPowers, Equivₓ.trans_apply, Equivₓ.trans_apply, fin_equiv_powers_symm_apply, ← Equivₓ.eq_symm_apply,
    fin_equiv_powers_symm_apply]
  simp [← h]

@[to_additive add_order_of_eq_card_multiples]
theorem order_eq_card_powers [DecidableEq G] : orderOf x = Fintype.card (Submonoid.powers x : Set G) :=
  (Fintype.card_fin (orderOf x)).symm.trans (Fintype.card_eq.2 ⟨finEquivPowers x⟩)

end FiniteCancelMonoid

section FiniteGroup

variable [Groupₓ G] [AddGroupₓ A]

@[to_additive]
theorem exists_zpow_eq_one (x : G) : ∃ (i : ℤ)(H : i ≠ 0), x ^ (i : ℤ) = 1 := by
  rcases exists_pow_eq_one x with ⟨w, hw1, hw2⟩
  refine' ⟨w, int.coe_nat_ne_zero.mpr (ne_of_gtₓ hw1), _⟩
  rw [zpow_coe_nat]
  exact (is_periodic_pt_mul_iff_pow_eq_one _).mp hw2

open Subgroup

@[to_additive mem_multiples_iff_mem_zmultiples]
theorem mem_powers_iff_mem_zpowers : y ∈ Submonoid.powers x ↔ y ∈ zpowers x :=
  ⟨fun ⟨n, hn⟩ =>
    ⟨n, by
      simp_all ⟩,
    fun ⟨i, hi⟩ =>
    ⟨(i % orderOf x).natAbs, by
      rwa [← zpow_coe_nat, Int.nat_abs_of_nonneg (Int.mod_nonneg _ (Int.coe_nat_ne_zero_iff_pos.2 (order_of_pos x))), ←
        zpow_eq_mod_order_of]⟩⟩

@[to_additive multiples_eq_zmultiples]
theorem powers_eq_zpowers (x : G) : (Submonoid.powers x : Set G) = zpowers x :=
  Set.ext fun x => mem_powers_iff_mem_zpowers

@[to_additive mem_zmultiples_iff_mem_range_add_order_of]
theorem mem_zpowers_iff_mem_range_order_of [DecidableEq G] :
    y ∈ Subgroup.zpowers x ↔ y ∈ (Finset.range (orderOf x)).Image ((· ^ ·) x : ℕ → G) := by
  rw [← mem_powers_iff_mem_zpowers, mem_powers_iff_mem_range_order_of]

@[to_additive decidableZmultiples]
noncomputable instance decidableZpowers [DecidableEq G] : DecidablePred (· ∈ Subgroup.zpowers x) := by
  simp_rw [← SetLike.mem_coe]
  rw [← powers_eq_zpowers]
  exact decidablePowers

/-- The equivalence between `fin (order_of x)` and `subgroup.zpowers x`, sending `i` to `x ^ i`. -/
@[to_additive finEquivZmultiples
      "The equivalence between `fin (add_order_of a)` and `subgroup.zmultiples a`, sending `i`\nto `i • a`."]
noncomputable def finEquivZpowers (x : G) : Finₓ (orderOf x) ≃ (Subgroup.zpowers x : Set G) :=
  (finEquivPowers x).trans (Equivₓ.Set.ofEq (powers_eq_zpowers x))

@[simp, to_additive fin_equiv_zmultiples_apply]
theorem fin_equiv_zpowers_apply {n : Finₓ (orderOf x)} : finEquivZpowers x n = ⟨x ^ (n : ℕ), n, zpow_coe_nat x n⟩ :=
  rfl

@[simp, to_additive fin_equiv_zmultiples_symm_apply]
theorem fin_equiv_zpowers_symm_apply (x : G) (n : ℕ) {hn : ∃ m : ℤ, x ^ m = x ^ n} :
    (finEquivZpowers x).symm ⟨x ^ n, hn⟩ = ⟨n % orderOf x, Nat.mod_ltₓ _ (order_of_pos x)⟩ := by
  rw [finEquivZpowers, Equivₓ.symm_trans_apply, Equivₓ.Set.of_eq_symm_apply]
  exact fin_equiv_powers_symm_apply x n

/-- The equivalence between `subgroup.zpowers` of two elements `x, y` of the same order, mapping
  `x ^ i` to `y ^ i`. -/
@[to_additive zmultiplesEquivZmultiples
      "The equivalence between `subgroup.zmultiples` of two elements `a, b` of the same additive order,\n  mapping `i • a` to `i • b`."]
noncomputable def zpowersEquivZpowers (h : orderOf x = orderOf y) :
    (Subgroup.zpowers x : Set G) ≃ (Subgroup.zpowers y : Set G) :=
  (finEquivZpowers x).symm.trans ((Finₓ.cast h).toEquiv.trans (finEquivZpowers y))

@[simp, to_additive zmultiples_equiv_zmultiples_apply]
theorem zpowers_equiv_zpowers_apply (h : orderOf x = orderOf y) (n : ℕ) :
    zpowersEquivZpowers h ⟨x ^ n, n, zpow_coe_nat x n⟩ = ⟨y ^ n, n, zpow_coe_nat y n⟩ := by
  rw [zpowersEquivZpowers, Equivₓ.trans_apply, Equivₓ.trans_apply, fin_equiv_zpowers_symm_apply, ← Equivₓ.eq_symm_apply,
    fin_equiv_zpowers_symm_apply]
  simp [← h]

@[to_additive add_order_eq_card_zmultiples]
theorem order_eq_card_zpowers [DecidableEq G] : orderOf x = Fintype.card (zpowers x) :=
  (Fintype.card_fin (orderOf x)).symm.trans (Fintype.card_eq.2 ⟨finEquivZpowers x⟩)

open QuotientGroup

-- TODO: use cardinal theory, introduce `card : set G → ℕ`, or setup decidability for cosets
@[to_additive add_order_of_dvd_card_univ]
theorem order_of_dvd_card_univ : orderOf x ∣ Fintype.card G := by
  classical
  have ft_prod : Fintype ((G ⧸ zpowers x) × zpowers x) := Fintype.ofEquiv G group_equiv_quotient_times_subgroup
  have ft_s : Fintype (zpowers x) := @Fintype.prodRight _ _ _ ft_prod _
  have ft_cosets : Fintype (G ⧸ zpowers x) := @Fintype.prodLeft _ _ _ ft_prod ⟨⟨1, (zpowers x).one_mem⟩⟩
  have eq₁ : Fintype.card G = @Fintype.card _ ft_cosets * @Fintype.card _ ft_s :=
    calc
      Fintype.card G = @Fintype.card _ ft_prod := @Fintype.card_congr _ _ _ ft_prod group_equiv_quotient_times_subgroup
      _ = @Fintype.card _ (@Prod.fintype _ _ ft_cosets ft_s) := congr_arg (@Fintype.card _) <| Subsingleton.elimₓ _ _
      _ = @Fintype.card _ ft_cosets * @Fintype.card _ ft_s := @Fintype.card_prod _ _ ft_cosets ft_s
      
  have eq₂ : orderOf x = @Fintype.card _ ft_s :=
    calc
      orderOf x = _ := order_eq_card_zpowers
      _ = _ := congr_arg (@Fintype.card _) <| Subsingleton.elimₓ _ _
      
  exact
    Dvd.intro (@Fintype.card (G ⧸ Subgroup.zpowers x) ft_cosets)
      (by
        rw [eq₁, eq₂, mul_comm])

@[simp, to_additive card_nsmul_eq_zero]
theorem pow_card_eq_one : x ^ Fintype.card G = 1 := by
  let ⟨m, hm⟩ := @order_of_dvd_card_univ _ x _ _
  simp [← hm, ← pow_mulₓ, ← pow_order_of_eq_one]

@[to_additive]
theorem Subgroup.pow_index_mem {G : Type _} [Groupₓ G] (H : Subgroup G) [Fintype (G ⧸ H)] [Normal H] (g : G) :
    g ^ index H ∈ H := by
  rw [← eq_one_iff, QuotientGroup.coe_pow H, index_eq_card, pow_card_eq_one]

@[to_additive]
theorem pow_eq_mod_card (n : ℕ) : x ^ n = x ^ (n % Fintype.card G) := by
  rw [pow_eq_mod_order_of, ← Nat.mod_mod_of_dvd n order_of_dvd_card_univ, ← pow_eq_mod_order_of]

@[to_additive]
theorem zpow_eq_mod_card (n : ℤ) : x ^ n = x ^ (n % Fintype.card G) := by
  rw [zpow_eq_mod_order_of, ← Int.mod_mod_of_dvd n (Int.coe_nat_dvd.2 order_of_dvd_card_univ), ← zpow_eq_mod_order_of]

/-- If `gcd(|G|,n)=1` then the `n`th power map is a bijection -/
@[to_additive "If `gcd(|G|,n)=1` then the smul by `n` is a bijection", simps]
def powCoprime (h : Nat.Coprime (Fintype.card G) n) : G ≃ G where
  toFun := fun g => g ^ n
  invFun := fun g => g ^ Nat.gcdB (Fintype.card G) n
  left_inv := fun g => by
    have key : g ^ _ = g ^ _ := congr_arg (fun n : ℤ => g ^ n) (Nat.gcd_eq_gcd_ab (Fintype.card G) n)
    rwa [zpow_add, zpow_mul, zpow_mul, zpow_coe_nat, zpow_coe_nat, zpow_coe_nat, h.gcd_eq_one, pow_oneₓ,
      pow_card_eq_one, one_zpow, one_mulₓ, eq_comm] at key
  right_inv := fun g => by
    have key : g ^ _ = g ^ _ := congr_arg (fun n : ℤ => g ^ n) (Nat.gcd_eq_gcd_ab (Fintype.card G) n)
    rwa [zpow_add, zpow_mul, zpow_mul', zpow_coe_nat, zpow_coe_nat, zpow_coe_nat, h.gcd_eq_one, pow_oneₓ,
      pow_card_eq_one, one_zpow, one_mulₓ, eq_comm] at key

@[simp, to_additive]
theorem pow_coprime_one (h : Nat.Coprime (Fintype.card G) n) : powCoprime h 1 = 1 :=
  one_pow n

@[simp, to_additive]
theorem pow_coprime_inv (h : Nat.Coprime (Fintype.card G) n) {g : G} : powCoprime h g⁻¹ = (powCoprime h g)⁻¹ :=
  inv_pow g n

@[to_additive add_inf_eq_bot_of_coprime]
theorem inf_eq_bot_of_coprime {G : Type _} [Groupₓ G] {H K : Subgroup G} [Fintype H] [Fintype K]
    (h : Nat.Coprime (Fintype.card H) (Fintype.card K)) : H⊓K = ⊥ := by
  refine' (H⊓K).eq_bot_iff_forall.mpr fun x hx => _
  rw [← order_of_eq_one_iff, ← Nat.dvd_one, ← h.gcd_eq_one, Nat.dvd_gcd_iffₓ]
  exact
    ⟨(congr_arg (· ∣ Fintype.card H) (order_of_subgroup ⟨x, hx.1⟩)).mpr order_of_dvd_card_univ,
      (congr_arg (· ∣ Fintype.card K) (order_of_subgroup ⟨x, hx.2⟩)).mpr order_of_dvd_card_univ⟩

variable (a)

/-- TODO: Generalise to `submonoid.powers`.-/
@[to_additive image_range_add_order_of]
theorem image_range_order_of [DecidableEq G] :
    Finset.image (fun i => x ^ i) (Finset.range (orderOf x)) = (zpowers x : Set G).toFinset := by
  ext x
  rw [Set.mem_to_finset, SetLike.mem_coe, mem_zpowers_iff_mem_range_order_of]

/-- TODO: Generalise to `finite_cancel_monoid`. -/
@[to_additive gcd_nsmul_card_eq_zero_iff]
theorem pow_gcd_card_eq_one_iff : x ^ n = 1 ↔ x ^ gcdₓ n (Fintype.card G) = 1 :=
  ⟨fun h => pow_gcd_eq_one _ h <| pow_card_eq_one, fun h => by
    let ⟨m, hm⟩ := gcd_dvd_leftₓ n (Fintype.card G)
    rw [hm, pow_mulₓ, h, one_pow]⟩

end FiniteGroup

end Fintype

section PowIsSubgroup

/-- A nonempty idempotent subset of a finite cancellative monoid is a submonoid -/
@[to_additive "A nonempty idempotent subset of a finite cancellative add monoid is a submonoid"]
def submonoidOfIdempotent {M : Type _} [LeftCancelMonoid M] [Fintype M] (S : Set M) (hS1 : S.Nonempty)
    (hS2 : S * S = S) : Submonoid M :=
  have pow_mem : ∀ a : M, a ∈ S → ∀ n : ℕ, a ^ (n + 1) ∈ S := fun a ha =>
    Nat.rec
      (by
        rwa [zero_addₓ, pow_oneₓ])
      fun n ih => (congr_arg2ₓ (· ∈ ·) (pow_succₓ a (n + 1)).symm hS2).mp (Set.mul_mem_mul ha ih)
  { Carrier := S,
    one_mem' := by
      obtain ⟨a, ha⟩ := hS1
      rw [← pow_order_of_eq_one a, ← tsub_add_cancel_of_le (succ_le_of_lt (order_of_pos a))]
      exact pow_mem a ha (orderOf a - 1),
    mul_mem' := fun a b ha hb => (congr_arg2ₓ (· ∈ ·) rfl hS2).mp (Set.mul_mem_mul ha hb) }

/-- A nonempty idempotent subset of a finite group is a subgroup -/
@[to_additive "A nonempty idempotent subset of a finite add group is a subgroup"]
def subgroupOfIdempotent {G : Type _} [Groupₓ G] [Fintype G] (S : Set G) (hS1 : S.Nonempty) (hS2 : S * S = S) :
    Subgroup G :=
  { submonoidOfIdempotent S hS1 hS2 with Carrier := S,
    inv_mem' := fun a ha =>
      show a⁻¹ ∈ submonoidOfIdempotent S hS1 hS2 by
        rw [← one_mulₓ a⁻¹, ← pow_oneₓ a, ← pow_order_of_eq_one a, ← pow_sub a (order_of_pos a)]
        exact pow_mem ha (orderOf a - 1) }

-- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Interactive.lean:71:16: TODO classical! not yet supported
/-- If `S` is a nonempty subset of a finite group `G`, then `S ^ |G|` is a subgroup -/
@[to_additive smulCardAddSubgroup
      "If `S` is a nonempty subset of a finite add group `G`,\n  then `|G| • S` is a subgroup",
  simps]
def powCardSubgroup {G : Type _} [Groupₓ G] [Fintype G] (S : Set G) (hS : S.Nonempty) : Subgroup G :=
  have one_mem : (1 : G) ∈ S ^ Fintype.card G := by
    obtain ⟨a, ha⟩ := hS
    rw [← pow_card_eq_one]
    exact Set.pow_mem_pow ha (Fintype.card G)
  subgroupOfIdempotent (S ^ Fintype.card G) ⟨1, one_mem⟩
    (by
      classical
      refine' (Set.eq_of_subset_of_card_le (Set.subset_mul_left _ one_mem) (ge_of_eq _)).symm
      simp_rw [← pow_addₓ, Groupₓ.card_pow_eq_card_pow_card_univ S (Fintype.card G) le_rfl,
        Groupₓ.card_pow_eq_card_pow_card_univ S (Fintype.card G + Fintype.card G) le_add_self])

end PowIsSubgroup

section LinearOrderedRing

variable [LinearOrderedRing G]

theorem order_of_abs_ne_one (h : abs x ≠ 1) : orderOf x = 0 := by
  rw [order_of_eq_zero_iff']
  intro n hn hx
  replace hx : abs x ^ n = 1 := by
    simpa only [← abs_one, ← abs_pow] using congr_arg abs hx
  cases' h.lt_or_lt with h h
  · exact ((pow_lt_one (abs_nonneg x) h hn.ne').Ne hx).elim
    
  · exact ((one_lt_pow h hn.ne').ne' hx).elim
    

theorem LinearOrderedRing.order_of_le_two : orderOf x ≤ 2 := by
  cases' ne_or_eq (abs x) 1 with h h
  · simp [← order_of_abs_ne_one h]
    
  rcases eq_or_eq_neg_of_abs_eq h with (rfl | rfl)
  · simp
    
  apply order_of_le_of_pow_eq_one <;> norm_num

end LinearOrderedRing

