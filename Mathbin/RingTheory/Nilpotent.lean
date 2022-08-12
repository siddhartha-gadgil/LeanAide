/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Data.Nat.Choose.Sum
import Mathbin.Algebra.Algebra.Bilinear
import Mathbin.RingTheory.Ideal.Operations

/-!
# Nilpotent elements

## Main definitions

  * `is_nilpotent`
  * `is_nilpotent_neg_iff`
  * `commute.is_nilpotent_add`
  * `commute.is_nilpotent_mul_left`
  * `commute.is_nilpotent_mul_right`
  * `commute.is_nilpotent_sub`

-/


universe u v

variable {R S : Type u} {x y : R}

/-- An element is said to be nilpotent if some natural-number-power of it equals zero.

Note that we require only the bare minimum assumptions for the definition to make sense. Even
`monoid_with_zero` is too strong since nilpotency is important in the study of rings that are only
power-associative. -/
def IsNilpotent [Zero R] [Pow R ℕ] (x : R) : Prop :=
  ∃ n : ℕ, x ^ n = 0

theorem IsNilpotent.mk [Zero R] [Pow R ℕ] (x : R) (n : ℕ) (e : x ^ n = 0) : IsNilpotent x :=
  ⟨n, e⟩

theorem IsNilpotent.zero [MonoidWithZeroₓ R] : IsNilpotent (0 : R) :=
  ⟨1, pow_oneₓ 0⟩

theorem IsNilpotent.neg [Ringₓ R] (h : IsNilpotent x) : IsNilpotent (-x) := by
  obtain ⟨n, hn⟩ := h
  use n
  rw [neg_pow, hn, mul_zero]

@[simp]
theorem is_nilpotent_neg_iff [Ringₓ R] : IsNilpotent (-x) ↔ IsNilpotent x :=
  ⟨fun h => neg_negₓ x ▸ h.neg, fun h => h.neg⟩

theorem IsNilpotent.map [MonoidWithZeroₓ R] [MonoidWithZeroₓ S] {r : R} {F : Type _} [MonoidWithZeroHomClass F R S]
    (hr : IsNilpotent r) (f : F) : IsNilpotent (f r) := by
  use hr.some
  rw [← map_pow, hr.some_spec, map_zero]

/-- A structure that has zero and pow is reduced if it has no nonzero nilpotent elements. -/
class IsReduced (R : Type _) [Zero R] [Pow R ℕ] : Prop where
  eq_zero : ∀ x : R, IsNilpotent x → x = 0

instance (priority := 900) is_reduced_of_no_zero_divisors [MonoidWithZeroₓ R] [NoZeroDivisors R] : IsReduced R :=
  ⟨fun _ ⟨_, hn⟩ => pow_eq_zero hn⟩

instance (priority := 900) is_reduced_of_subsingleton [Zero R] [Pow R ℕ] [Subsingleton R] : IsReduced R :=
  ⟨fun _ _ => Subsingleton.elimₓ _ _⟩

theorem IsNilpotent.eq_zero [Zero R] [Pow R ℕ] [IsReduced R] (h : IsNilpotent x) : x = 0 :=
  IsReduced.eq_zero x h

@[simp]
theorem is_nilpotent_iff_eq_zero [MonoidWithZeroₓ R] [IsReduced R] : IsNilpotent x ↔ x = 0 :=
  ⟨fun h => h.eq_zero, fun h => h.symm ▸ IsNilpotent.zero⟩

theorem is_reduced_of_injective [MonoidWithZeroₓ R] [MonoidWithZeroₓ S] {F : Type _} [MonoidWithZeroHomClass F R S]
    (f : F) (hf : Function.Injective f) [IsReduced S] : IsReduced R := by
  constructor
  intro x hx
  apply hf
  rw [map_zero]
  exact (hx.map f).eq_zero

namespace Commute

section Semiringₓ

variable [Semiringₓ R] (h_comm : Commute x y)

include h_comm

theorem is_nilpotent_add (hx : IsNilpotent x) (hy : IsNilpotent y) : IsNilpotent (x + y) := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  use n + m - 1
  rw [h_comm.add_pow']
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  suffices x ^ i * y ^ j = 0 by
    simp only [← this, ← nsmul_eq_mul, ← mul_zero]
  cases' Nat.le_or_le_of_add_eq_add_pred (finset.nat.mem_antidiagonal.mp hij) with hi hj
  · rw [pow_eq_zero_of_le hi hn, zero_mul]
    
  · rw [pow_eq_zero_of_le hj hm, mul_zero]
    

theorem is_nilpotent_mul_left (h : IsNilpotent x) : IsNilpotent (x * y) := by
  obtain ⟨n, hn⟩ := h
  use n
  rw [h_comm.mul_pow, hn, zero_mul]

theorem is_nilpotent_mul_right (h : IsNilpotent y) : IsNilpotent (x * y) := by
  rw [h_comm.eq]
  exact h_comm.symm.is_nilpotent_mul_left h

end Semiringₓ

section Ringₓ

variable [Ringₓ R] (h_comm : Commute x y)

include h_comm

theorem is_nilpotent_sub (hx : IsNilpotent x) (hy : IsNilpotent y) : IsNilpotent (x - y) := by
  rw [← neg_right_iff] at h_comm
  rw [← is_nilpotent_neg_iff] at hy
  rw [sub_eq_add_neg]
  exact h_comm.is_nilpotent_add hx hy

end Ringₓ

end Commute

section CommSemiringₓ

variable [CommSemiringₓ R]

/-- The nilradical of a commutative semiring is the ideal of nilpotent elements. -/
def nilradical (R : Type _) [CommSemiringₓ R] : Ideal R :=
  (0 : Ideal R).radical

theorem mem_nilradical : x ∈ nilradical R ↔ IsNilpotent x :=
  Iff.rfl

theorem nilradical_eq_Inf (R : Type _) [CommSemiringₓ R] : nilradical R = inf { J : Ideal R | J.IsPrime } :=
  (Ideal.radical_eq_Inf ⊥).trans <| by
    simp_rw [and_iff_right bot_le]

theorem nilpotent_iff_mem_prime : IsNilpotent x ↔ ∀ J : Ideal R, J.IsPrime → x ∈ J := by
  rw [← mem_nilradical, nilradical_eq_Inf, Submodule.mem_Inf]
  rfl

theorem nilradical_le_prime (J : Ideal R) [H : J.IsPrime] : nilradical R ≤ J :=
  (nilradical_eq_Inf R).symm ▸ Inf_le H

@[simp]
theorem nilradical_eq_zero (R : Type _) [CommSemiringₓ R] [IsReduced R] : nilradical R = 0 :=
  Ideal.ext fun _ => is_nilpotent_iff_eq_zero

end CommSemiringₓ

namespace Algebra

variable (R) {A : Type v} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

@[simp]
theorem is_nilpotent_lmul_left_iff (a : A) : IsNilpotent (lmulLeft R a) ↔ IsNilpotent a := by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;> simp only [← lmul_left_eq_zero_iff, ← pow_lmul_left] at hn⊢ <;> exact hn

@[simp]
theorem is_nilpotent_lmul_right_iff (a : A) : IsNilpotent (lmulRight R a) ↔ IsNilpotent a := by
  constructor <;>
    rintro ⟨n, hn⟩ <;> use n <;> simp only [← lmul_right_eq_zero_iff, ← pow_lmul_right] at hn⊢ <;> exact hn

end Algebra

namespace Module.End

variable {M : Type v} [Ringₓ R] [AddCommGroupₓ M] [Module R M]

variable {f : Module.End R M} {p : Submodule R M} (hp : p ≤ p.comap f)

theorem IsNilpotent.mapq (hnp : IsNilpotent f) : IsNilpotent (p.mapq p f hp) := by
  obtain ⟨k, hk⟩ := hnp
  use k
  simp [p.mapq_pow, ← hk]

end Module.End

