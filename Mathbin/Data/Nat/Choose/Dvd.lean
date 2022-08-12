/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens
-/
import Mathbin.Data.Nat.Choose.Basic
import Mathbin.Data.Nat.Prime

/-!
# Divisibility properties of binomial coefficients
-/


namespace Nat

open Nat

namespace Prime

theorem dvd_choose_add {p a b : ℕ} (hap : a < p) (hbp : b < p) (h : p ≤ a + b) (hp : Prime p) : p ∣ choose (a + b) a :=
  by
  have h₁ : p ∣ (a + b)! := hp.dvd_factorial.2 h
  have h₂ : ¬p ∣ a ! := mt hp.dvd_factorial.1 (not_le_of_gtₓ hap)
  have h₃ : ¬p ∣ b ! := mt hp.dvd_factorial.1 (not_le_of_gtₓ hbp)
  rw [← choose_mul_factorial_mul_factorial (le.intro rfl), mul_assoc, hp.dvd_mul, hp.dvd_mul,
      add_tsub_cancel_left a b] at h₁ <;>
    exact h₁.resolve_right (not_or_distrib.2 ⟨h₂, h₃⟩)

theorem dvd_choose_self {p k : ℕ} (hk : 0 < k) (hkp : k < p) (hp : Prime p) : p ∣ choose p k := by
  have r : k + (p - k) = p := by
    rw [← add_tsub_assoc_of_le (Nat.le_of_ltₓ hkp) k, add_tsub_cancel_left]
  have e : p ∣ choose (k + (p - k)) k :=
    dvd_choose_add hkp (Nat.sub_ltₓ (hk.trans hkp) hk)
      (by
        rw [r])
      hp
  rwa [r] at e

end Prime

end Nat

