/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Devon Tuma
-/
import Mathbin.GroupTheory.Submonoid.Operations
import Mathbin.GroupTheory.Submonoid.Membership

/-!
# Non-zero divisors

In this file we define the submonoid `non_zero_divisors` of a `monoid_with_zero`.

## Notations

This file declares the notation `R⁰` for the submonoid of non-zero-divisors of `R`,
in the locale `non_zero_divisors`. Use the statement `open_locale non_zero_divisors`
to access this notation in your own code.

-/


section nonZeroDivisors

/-- The submonoid of non-zero-divisors of a `monoid_with_zero` `R`. -/
def nonZeroDivisors (R : Type _) [MonoidWithZeroₓ R] : Submonoid R where
  Carrier := { x | ∀ z, z * x = 0 → z = 0 }
  one_mem' := fun z hz => by
    rwa [mul_oneₓ] at hz
  mul_mem' := fun x₁ x₂ hx₁ hx₂ z hz =>
    have : z * x₁ * x₂ = 0 := by
      rwa [mul_assoc]
    hx₁ z <| hx₂ (z * x₁) this

-- mathport name: «expr ⁰»
localized [nonZeroDivisors] notation:9000 R "⁰" => nonZeroDivisors R

variable {M M' M₁ R R' F : Type _} [MonoidWithZeroₓ M] [MonoidWithZeroₓ M'] [CommMonoidWithZero M₁] [Ringₓ R]
  [CommRingₓ R']

theorem mem_non_zero_divisors_iff {r : M} : r ∈ M⁰ ↔ ∀ x, x * r = 0 → x = 0 :=
  Iff.rfl

theorem mul_right_mem_non_zero_divisors_eq_zero_iff {x r : M} (hr : r ∈ M⁰) : x * r = 0 ↔ x = 0 :=
  ⟨hr _, by
    simp (config := { contextual := true })⟩

@[simp]
theorem mul_right_coe_non_zero_divisors_eq_zero_iff {x : M} {c : M⁰} : x * c = 0 ↔ x = 0 :=
  mul_right_mem_non_zero_divisors_eq_zero_iff c.Prop

theorem mul_left_mem_non_zero_divisors_eq_zero_iff {r x : M₁} (hr : r ∈ M₁⁰) : r * x = 0 ↔ x = 0 := by
  rw [mul_comm, mul_right_mem_non_zero_divisors_eq_zero_iff hr]

@[simp]
theorem mul_left_coe_non_zero_divisors_eq_zero_iff {c : M₁⁰} {x : M₁} : (c : M₁) * x = 0 ↔ x = 0 :=
  mul_left_mem_non_zero_divisors_eq_zero_iff c.Prop

theorem mul_cancel_right_mem_non_zero_divisor {x y r : R} (hr : r ∈ R⁰) : x * r = y * r ↔ x = y := by
  refine' ⟨fun h => _, congr_arg _⟩
  rw [← sub_eq_zero, ← mul_right_mem_non_zero_divisors_eq_zero_iff hr, sub_mul, h, sub_self]

theorem mul_cancel_right_coe_non_zero_divisor {x y : R} {c : R⁰} : x * c = y * c ↔ x = y :=
  mul_cancel_right_mem_non_zero_divisor c.Prop

@[simp]
theorem mul_cancel_left_mem_non_zero_divisor {x y r : R'} (hr : r ∈ R'⁰) : r * x = r * y ↔ x = y := by
  simp_rw [mul_comm r, mul_cancel_right_mem_non_zero_divisor hr]

theorem mul_cancel_left_coe_non_zero_divisor {x y : R'} {c : R'⁰} : (c : R') * x = c * y ↔ x = y :=
  mul_cancel_left_mem_non_zero_divisor c.Prop

theorem nonZeroDivisors.ne_zero [Nontrivial M] {x} (hx : x ∈ M⁰) : x ≠ 0 := fun h =>
  one_ne_zero (hx _ <| (one_mulₓ _).trans h)

theorem nonZeroDivisors.coe_ne_zero [Nontrivial M] (x : M⁰) : (x : M) ≠ 0 :=
  nonZeroDivisors.ne_zero x.2

theorem mul_mem_non_zero_divisors {a b : M₁} : a * b ∈ M₁⁰ ↔ a ∈ M₁⁰ ∧ b ∈ M₁⁰ := by
  constructor
  · intro h
    constructor <;> intro x h' <;> apply h
    · rw [← mul_assoc, h', zero_mul]
      
    · rw [mul_comm a b, ← mul_assoc, h', zero_mul]
      
    
  · rintro ⟨ha, hb⟩ x hx
    apply ha
    apply hb
    rw [mul_assoc, hx]
    

theorem is_unit_of_mem_non_zero_divisors {G₀ : Type _} [GroupWithZeroₓ G₀] {x : G₀} (hx : x ∈ nonZeroDivisors G₀) :
    IsUnit x :=
  ⟨⟨x, x⁻¹, mul_inv_cancel (nonZeroDivisors.ne_zero hx), inv_mul_cancel (nonZeroDivisors.ne_zero hx)⟩, rfl⟩

theorem eq_zero_of_ne_zero_of_mul_right_eq_zero [NoZeroDivisors M] {x y : M} (hnx : x ≠ 0) (hxy : y * x = 0) : y = 0 :=
  Or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx

theorem eq_zero_of_ne_zero_of_mul_left_eq_zero [NoZeroDivisors M] {x y : M} (hnx : x ≠ 0) (hxy : x * y = 0) : y = 0 :=
  Or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx

theorem mem_non_zero_divisors_of_ne_zero [NoZeroDivisors M] {x : M} (hx : x ≠ 0) : x ∈ M⁰ := fun _ =>
  eq_zero_of_ne_zero_of_mul_right_eq_zero hx

theorem mem_non_zero_divisors_iff_ne_zero [NoZeroDivisors M] [Nontrivial M] {x : M} : x ∈ M⁰ ↔ x ≠ 0 :=
  ⟨nonZeroDivisors.ne_zero, mem_non_zero_divisors_of_ne_zero⟩

theorem map_ne_zero_of_mem_non_zero_divisors [Nontrivial M] [ZeroHomClass F M M'] (g : F)
    (hg : Function.Injective (g : M → M')) {x : M} (h : x ∈ M⁰) : g x ≠ 0 := fun h0 =>
  one_ne_zero (h 1 ((one_mulₓ x).symm ▸ hg (trans h0 (map_zero g).symm)))

theorem map_mem_non_zero_divisors [Nontrivial M] [NoZeroDivisors M'] [ZeroHomClass F M M'] (g : F)
    (hg : Function.Injective g) {x : M} (h : x ∈ M⁰) : g x ∈ M'⁰ := fun z hz =>
  eq_zero_of_ne_zero_of_mul_right_eq_zero (map_ne_zero_of_mem_non_zero_divisors g hg h) hz

theorem le_non_zero_divisors_of_no_zero_divisors [NoZeroDivisors M] {S : Submonoid M} (hS : (0 : M) ∉ S) : S ≤ M⁰ :=
  fun x hx y hy =>
  Or.rec_on (eq_zero_or_eq_zero_of_mul_eq_zero hy) (fun h => h) fun h => absurd (h ▸ hx : (0 : M) ∈ S) hS

theorem powers_le_non_zero_divisors_of_no_zero_divisors [NoZeroDivisors M] {a : M} (ha : a ≠ 0) :
    Submonoid.powers a ≤ M⁰ :=
  le_non_zero_divisors_of_no_zero_divisors fun h => absurd (h.recOn fun _ hn => pow_eq_zero hn) ha

theorem map_le_non_zero_divisors_of_injective [NoZeroDivisors M'] [MonoidWithZeroHomClass F M M'] (f : F)
    (hf : Function.Injective f) {S : Submonoid M} (hS : S ≤ M⁰) : S.map f ≤ M'⁰ := by
  cases subsingleton_or_nontrivial M
  · simp [← Subsingleton.elimₓ S ⊥]
    
  · exact
      le_non_zero_divisors_of_no_zero_divisors fun h =>
        let ⟨x, hx, hx0⟩ := h
        zero_ne_one (hS (hf (trans hx0 (map_zero f).symm) ▸ hx : 0 ∈ S) 1 (mul_zero 1)).symm
    

theorem non_zero_divisors_le_comap_non_zero_divisors_of_injective [NoZeroDivisors M'] [MonoidWithZeroHomClass F M M']
    (f : F) (hf : Function.Injective f) : M⁰ ≤ M'⁰.comap f :=
  Submonoid.le_comap_of_map_le _ (map_le_non_zero_divisors_of_injective _ hf le_rfl)

theorem prod_zero_iff_exists_zero [NoZeroDivisors M₁] [Nontrivial M₁] {s : Multiset M₁} :
    s.Prod = 0 ↔ ∃ (r : M₁)(hr : r ∈ s), r = 0 := by
  constructor
  swap
  · rintro ⟨r, hrs, rfl⟩
    exact Multiset.prod_eq_zero hrs
    
  refine' Multiset.induction _ (fun a s ih => _) s
  · intro habs
    simpa using habs
    
  · rw [Multiset.prod_cons]
    intro hprod
    replace hprod := eq_zero_or_eq_zero_of_mul_eq_zero hprod
    cases' hprod with ha
    · exact ⟨a, Multiset.mem_cons_self a s, ha⟩
      
    · apply (ih hprod).imp _
      rintro b ⟨hb₁, hb₂⟩
      exact ⟨Multiset.mem_cons_of_mem hb₁, hb₂⟩
      
    

end nonZeroDivisors

