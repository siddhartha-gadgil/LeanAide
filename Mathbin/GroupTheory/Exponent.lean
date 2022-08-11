/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Mathbin.GroupTheory.OrderOfElement
import Mathbin.Algebra.PunitInstances
import Mathbin.Algebra.GcdMonoid.Finset
import Mathbin.Tactic.ByContra
import Mathbin.NumberTheory.Padics.PadicVal

/-!
# Exponent of a group

This file defines the exponent of a group, or more generally a monoid. For a group `G` it is defined
to be the minimal `n≥1` such that `g ^ n = 1` for all `g ∈ G`. For a finite group `G`,
it is equal to the lowest common multiple of the order of all elements of the group `G`.

## Main definitions

* `monoid.exponent_exists` is a predicate on a monoid `G` saying that there is some positive `n`
  such that `g ^ n = 1` for all `g ∈ G`.
* `monoid.exponent` defines the exponent of a monoid `G` as the minimal positive `n` such that
  `g ^ n = 1` for all `g ∈ G`, by convention it is `0` if no such `n` exists.
* `add_monoid.exponent_exists` the additive version of `monoid.exponent_exists`.
* `add_monoid.exponent` the additive version of `monoid.exponent`.

## Main results

* `monoid.lcm_order_eq_exponent`: For a finite left cancel monoid `G`, the exponent is equal to the
  `finset.lcm` of the order of its elements.
* `monoid.exponent_eq_supr_order_of(')`: For a commutative cancel monoid, the exponent is
  equal to `⨆ g : G, order_of g` (or zero if it has any order-zero elements).

## TODO
* Refactor the characteristic of a ring to be the exponent of its underlying additive group.
-/


universe u

variable {G : Type u}

open Classical

namespace Monoidₓ

section Monoidₓ

variable (G) [Monoidₓ G]

/-- A predicate on a monoid saying that there is a positive integer `n` such that `g ^ n = 1`
  for all `g`.-/
@[to_additive
      "A predicate on an additive monoid saying that there is a positive integer `n` such\n  that `n • g = 0` for all `g`."]
def ExponentExists :=
  ∃ n, 0 < n ∧ ∀ g : G, g ^ n = 1

/-- The exponent of a group is the smallest positive integer `n` such that `g ^ n = 1` for all
  `g ∈ G` if it exists, otherwise it is zero by convention.-/
@[to_additive
      "The exponent of an additive group is the smallest positive integer `n` such that\n  `n • g = 0` for all `g ∈ G` if it exists, otherwise it is zero by convention."]
noncomputable def exponent :=
  if h : ExponentExists G then Nat.findₓ h else 0

variable {G}

@[to_additive]
theorem exponent_exists_iff_ne_zero : ExponentExists G ↔ exponent G ≠ 0 := by
  rw [exponent]
  split_ifs
  · simp [← h, ← @not_lt_zero' ℕ]
    
  --if this isn't done this way, `to_additive` freaks
  · tauto
    

@[to_additive]
theorem exponent_eq_zero_iff : exponent G = 0 ↔ ¬ExponentExists G := by
  simp only [← exponent_exists_iff_ne_zero, ← not_not]

@[to_additive]
theorem exponent_eq_zero_of_order_zero {g : G} (hg : orderOf g = 0) : exponent G = 0 :=
  exponent_eq_zero_iff.mpr fun ⟨n, hn, hgn⟩ => order_of_eq_zero_iff'.mp hg n hn <| hgn g

@[to_additive exponent_nsmul_eq_zero]
theorem pow_exponent_eq_one (g : G) : g ^ exponent G = 1 := by
  by_cases' exponent_exists G
  · simp_rw [exponent, dif_pos h]
    exact (Nat.find_specₓ h).2 g
    
  · simp_rw [exponent, dif_neg h, pow_zeroₓ]
    

@[to_additive]
theorem pow_eq_mod_exponent {n : ℕ} (g : G) : g ^ n = g ^ (n % exponent G) :=
  calc
    g ^ n = g ^ (n % exponent G + exponent G * (n / exponent G)) := by
      rw [Nat.mod_add_divₓ]
    _ = g ^ (n % exponent G) := by
      simp [← pow_addₓ, ← pow_mulₓ, ← pow_exponent_eq_one]
    

@[to_additive]
theorem exponent_pos_of_exists (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, g ^ n = 1) : 0 < exponent G := by
  have h : ∃ n, 0 < n ∧ ∀ g : G, g ^ n = 1 := ⟨n, hpos, hG⟩
  rw [exponent, dif_pos]
  exact (Nat.find_specₓ h).1

@[to_additive]
theorem exponent_min' (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, g ^ n = 1) : exponent G ≤ n := by
  rw [exponent, dif_pos]
  · apply Nat.find_min'ₓ
    exact ⟨hpos, hG⟩
    
  · exact ⟨n, hpos, hG⟩
    

@[to_additive]
theorem exponent_min (m : ℕ) (hpos : 0 < m) (hm : m < exponent G) : ∃ g : G, g ^ m ≠ 1 := by
  by_contra' h
  have hcon : exponent G ≤ m := exponent_min' m hpos h
  linarith

@[simp, to_additive]
theorem exp_eq_one_of_subsingleton [Subsingleton G] : exponent G = 1 := by
  apply le_antisymmₓ
  · apply exponent_min' _ Nat.one_posₓ
    simp
    
  · apply Nat.succ_le_of_ltₓ
    apply exponent_pos_of_exists 1 Nat.one_posₓ
    simp
    

@[to_additive add_order_dvd_exponent]
theorem order_dvd_exponent (g : G) : orderOf g ∣ exponent G :=
  order_of_dvd_of_pow_eq_one <| pow_exponent_eq_one g

variable (G)

@[to_additive]
theorem exponent_dvd_of_forall_pow_eq_one (G) [Monoidₓ G] (n : ℕ) (hG : ∀ g : G, g ^ n = 1) : exponent G ∣ n := by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · exact dvd_zero _
    
  apply Nat.dvd_of_mod_eq_zeroₓ
  by_contra h
  have h₁ := Nat.pos_of_ne_zeroₓ h
  have h₂ : n % exponent G < exponent G := Nat.mod_ltₓ _ (exponent_pos_of_exists n hpos hG)
  have h₃ : exponent G ≤ n % exponent G := by
    apply exponent_min' _ h₁
    simp_rw [← pow_eq_mod_exponent]
    exact hG
  linarith

@[to_additive lcm_add_order_of_dvd_exponent]
theorem lcm_order_of_dvd_exponent [Fintype G] : (Finset.univ : Finset G).lcm orderOf ∣ exponent G := by
  apply Finset.lcm_dvd
  intro g hg
  exact order_dvd_exponent g

@[to_additive exists_order_of_eq_pow_padic_val_nat_add_exponent]
theorem _root_.nat.prime.exists_order_of_eq_pow_factorization_exponent {p : ℕ} (hp : p.Prime) :
    ∃ g : G, orderOf g = p ^ (exponent G).factorization p := by
  have := Fact.mk hp
  rcases eq_or_ne ((exponent G).factorization p) 0 with (h | h)
  · refine'
      ⟨1, by
        rw [h, pow_zeroₓ, order_of_one]⟩
    
  have he : 0 < exponent G :=
    Ne.bot_lt fun ht => by
      rw [ht] at h
      apply h
      rw [bot_eq_zero, Nat.factorization_zero, Finsupp.zero_apply]
  rw [← Finsupp.mem_support_iff] at h
  obtain ⟨g, hg⟩ : ∃ g : G, g ^ (exponent G / p) ≠ 1 := by
    suffices key : ¬exponent G ∣ exponent G / p
    · simpa using mt (exponent_dvd_of_forall_pow_eq_one G (exponent G / p)) key
      
    exact fun hd =>
      hp.one_lt.not_le
        ((mul_le_iff_le_one_left he).mp <|
          Nat.le_of_dvdₓ he <| Nat.mul_dvd_of_dvd_div (Nat.dvd_of_mem_factorization h) hd)
  obtain ⟨k, hk : exponent G = p ^ _ * k⟩ := Nat.pow_factorization_dvd _ _
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (finsupp.mem_support_iff.mp h)
  refine' ⟨g ^ k, _⟩
  rw [ht]
  apply order_of_eq_prime_pow
  · rwa [hk, mul_comm, ht, pow_succ'ₓ, ← mul_assoc, Nat.mul_div_cancelₓ _ hp.pos, pow_mulₓ] at hg
    
  · rw [← Nat.succ_eq_add_one, ← ht, ← pow_mulₓ, mul_comm, ← hk]
    exact pow_exponent_eq_one g
    

variable {G}

@[to_additive]
theorem exponent_ne_zero_iff_range_order_of_finite (h : ∀ g : G, 0 < orderOf g) :
    exponent G ≠ 0 ↔ (Set.Range (orderOf : G → ℕ)).Finite := by
  refine' ⟨fun he => _, fun he => _⟩
  · by_contra h
    obtain ⟨m, ⟨t, rfl⟩, het⟩ := Set.Infinite.exists_nat_lt h (exponent G)
    exact pow_ne_one_of_lt_order_of' he het (pow_exponent_eq_one t)
    
  · lift Set.Range orderOf to Finset ℕ using he with t ht
    have htpos : 0 < t.prod id := by
      refine' Finset.prod_pos fun a ha => _
      rw [← Finset.mem_coe, ht] at ha
      obtain ⟨k, rfl⟩ := ha
      exact h k
    suffices exponent G ∣ t.prod id by
      intro h
      rw [h, zero_dvd_iff] at this
      exact htpos.ne' this
    refine' exponent_dvd_of_forall_pow_eq_one _ _ fun g => _
    rw [pow_eq_mod_order_of, Nat.mod_eq_zero_of_dvdₓ, pow_zeroₓ g]
    apply Finset.dvd_prod_of_mem
    rw [← Finset.mem_coe, ht]
    exact Set.mem_range_self g
    

@[to_additive]
theorem exponent_eq_zero_iff_range_order_of_infinite (h : ∀ g : G, 0 < orderOf g) :
    exponent G = 0 ↔ (Set.Range (orderOf : G → ℕ)).Infinite := by
  have := exponent_ne_zero_iff_range_order_of_finite h
  rwa [Ne.def, not_iff_comm, Iff.comm] at this

@[to_additive lcm_add_order_eq_exponent]
theorem lcm_order_eq_exponent [Fintype G] : (Finset.univ : Finset G).lcm orderOf = exponent G := by
  apply Nat.dvd_antisymm (lcm_order_of_dvd_exponent G)
  refine' exponent_dvd_of_forall_pow_eq_one G _ fun g => _
  obtain ⟨m, hm⟩ : orderOf g ∣ finset.univ.lcm orderOf := Finset.dvd_lcm (Finset.mem_univ g)
  rw [hm, pow_mulₓ, pow_order_of_eq_one, one_pow]

end Monoidₓ

section LeftCancelMonoid

variable [LeftCancelMonoid G]

@[to_additive]
theorem exponent_ne_zero_of_fintype [Fintype G] : exponent G ≠ 0 := by
  simpa [lcm_order_eq_exponent, ← Finset.lcm_eq_zero_iff] using fun x => (order_of_pos x).ne'

end LeftCancelMonoid

section CommMonoidₓ

variable [CommMonoidₓ G]

@[to_additive]
theorem exponent_eq_supr_order_of (h : ∀ g : G, 0 < orderOf g) : exponent G = ⨆ g : G, orderOf g := by
  rw [supr]
  rcases eq_or_ne (exponent G) 0 with (he | he)
  · rw [he, Set.Infinite.Nat.Sup_eq_zero <| (exponent_eq_zero_iff_range_order_of_infinite h).1 he]
    
  have hne : (Set.Range (orderOf : G → ℕ)).Nonempty := ⟨1, 1, order_of_one⟩
  have hfin : (Set.Range (orderOf : G → ℕ)).Finite := by
    rwa [← exponent_ne_zero_iff_range_order_of_finite h]
  obtain ⟨t, ht⟩ := hne.cSup_mem hfin
  apply Nat.dvd_antisymm _
  · rw [← ht]
    apply order_dvd_exponent
    
  refine' Nat.dvd_of_factors_subperm he _
  rw [List.subperm_ext_iff]
  by_contra' h
  obtain ⟨p, hp, hpe⟩ := h
  replace hp := Nat.prime_of_mem_factors hp
  simp only [← Nat.factors_count_eq] at hpe
  set k := (orderOf t).factorization p with hk
  obtain ⟨g, hg⟩ := hp.exists_order_of_eq_pow_factorization_exponent G
  suffices orderOf t < orderOf (t ^ p ^ k * g) by
    rw [ht] at this
    exact this.not_le (le_cSup hfin.bdd_above <| Set.mem_range_self _)
  have hpk : p ^ k ∣ orderOf t := Nat.pow_factorization_dvd _ _
  have hpk' : orderOf (t ^ p ^ k) = orderOf t / p ^ k := by
    rw [order_of_pow' t (pow_ne_zero k hp.ne_zero), Nat.gcd_eq_rightₓ hpk]
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_lt hpe
  have hcoprime : (orderOf (t ^ p ^ k)).Coprime (orderOf g) := by
    rw [hg, Nat.coprime_pow_right_iff (pos_of_gt hpe), Nat.coprime_commₓ]
    apply Or.resolve_right (Nat.coprime_or_dvd_of_prime hp _)
    nth_rw 0[← pow_oneₓ p]
    convert Nat.pow_succ_factorization_not_dvd (h <| t ^ p ^ k).ne' hp
    rw [hpk', Nat.factorization_div hpk]
    simp [← hp]
  rw [(Commute.all _ g).order_of_mul_eq_mul_order_of_of_coprime hcoprime, hpk', hg, ha, ← ht, ← hk, pow_addₓ, pow_addₓ,
    pow_oneₓ, ← mul_assoc, ← mul_assoc, Nat.div_mul_cancelₓ, mul_assoc, lt_mul_iff_one_lt_right <| h t, ← pow_succ'ₓ]
  exact one_lt_pow hp.one_lt a.succ_ne_zero
  exact hpk

@[to_additive]
theorem exponent_eq_supr_order_of' : exponent G = if ∃ g : G, orderOf g = 0 then 0 else ⨆ g : G, orderOf g := by
  split_ifs
  · obtain ⟨g, hg⟩ := h
    exact exponent_eq_zero_of_order_zero hg
    
  · have := not_exists.mp h
    exact exponent_eq_supr_order_of fun g => Ne.bot_lt <| this g
    

end CommMonoidₓ

section CancelCommMonoid

variable [CancelCommMonoid G]

@[to_additive]
theorem exponent_eq_max'_order_of [Fintype G] :
    exponent G =
      ((@Finset.univ G _).Image orderOf).max'
        ⟨1, by
          simp ⟩ :=
  by
  rw [← Finset.Nonempty.cSup_eq_max', Finset.coe_image, Finset.coe_univ, Set.image_univ, ← supr]
  exact exponent_eq_supr_order_of order_of_pos

end CancelCommMonoid

end Monoidₓ

