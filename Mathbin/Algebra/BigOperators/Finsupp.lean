/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Data.Finsupp.Basic
import Mathbin.Algebra.BigOperators.Pi
import Mathbin.Algebra.BigOperators.Ring
import Mathbin.Algebra.BigOperators.Order

/-!
# Big operators for finsupps

This file contains theorems relevant to big operators in finitely supported functions.
-/


open BigOperators

variable {α ι γ A B C : Type _} [AddCommMonoidₓ A] [AddCommMonoidₓ B] [AddCommMonoidₓ C]

variable {t : ι → A → C} (h0 : ∀ i, t i 0 = 0) (h1 : ∀ i x y, t i (x + y) = t i x + t i y)

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

theorem Finset.sum_apply' : (∑ k in s, f k) i = ∑ k in s, f k i :=
  (Finsupp.applyAddHom i : (ι →₀ A) →+ A).map_sum f s

theorem Finsupp.sum_apply' : g.Sum k x = g.Sum fun i b => k i b x :=
  Finset.sum_apply _ _ _

section

include h0 h1

open Classical

theorem Finsupp.sum_sum_index' : (∑ x in s, f x).Sum t = ∑ x in s, (f x).Sum t :=
  (Finset.induction_on s rfl) fun a s has ih => by
    simp_rw [Finset.sum_insert has, Finsupp.sum_add_index' h0 h1, ih]

end

section

variable {R S : Type _} [NonUnitalNonAssocSemiringₓ R] [NonUnitalNonAssocSemiringₓ S]

theorem Finsupp.sum_mul (b : S) (s : α →₀ R) {f : α → R → S} : s.Sum f * b = s.Sum fun a c => f a c * b := by
  simp only [← Finsupp.sum, ← Finset.sum_mul]

theorem Finsupp.mul_sum (b : S) (s : α →₀ R) {f : α → R → S} : b * s.Sum f = s.Sum fun a c => b * f a c := by
  simp only [← Finsupp.sum, ← Finset.mul_sum]

end

namespace Nat

/-- If `0 : ℕ` is not in the support of `f : ℕ →₀ ℕ` then `0 < ∏ x in f.support, x ^ (f x)`. -/
theorem prod_pow_pos_of_zero_not_mem_support {f : ℕ →₀ ℕ} (hf : 0 ∉ f.Support) : 0 < f.Prod pow :=
  Finset.prod_pos fun a ha =>
    pos_iff_ne_zero.mpr
      (pow_ne_zero _ fun H => by
        subst H
        exact hf ha)

end Nat

