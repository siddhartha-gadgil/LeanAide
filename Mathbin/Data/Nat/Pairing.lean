/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathbin.Data.Nat.Sqrt
import Mathbin.Data.Set.Lattice

/-!
#  Naturals pairing function

This file defines a pairing function for the naturals as follows:
```text
 0  1  4  9 16
 2  3  5 10 17
 6  7  8 11 18
12 13 14 15 19
20 21 22 23 24
```

It has the advantage of being monotone in both directions and sending `⟦0, n^2 - 1⟧` to
`⟦0, n - 1⟧²`.
-/


open Prod Decidable Function

namespace Nat

/-- Pairing function for the natural numbers. -/
@[pp_nodot]
def mkpair (a b : ℕ) : ℕ :=
  if a < b then b * b + a else a * a + a + b

/-- Unpairing function for the natural numbers. -/
@[pp_nodot]
def unpair (n : ℕ) : ℕ × ℕ :=
  let s := sqrt n
  if n - s * s < s then (n - s * s, s) else (s, n - s * s - s)

@[simp]
theorem mkpair_unpair (n : ℕ) : mkpair (unpair n).1 (unpair n).2 = n := by
  dsimp' only [← unpair]
  set s := sqrt n
  have sm : s * s + (n - s * s) = n := add_tsub_cancel_of_le (sqrt_le _)
  split_ifs
  · simp [← mkpair, ← h, ← sm]
    
  · have hl : n - s * s - s ≤ s :=
      tsub_le_iff_left.mpr
        (tsub_le_iff_left.mpr <| by
          rw [← add_assocₓ] <;> apply sqrt_le_add)
    simp [← mkpair, ← hl.not_lt, ← add_assocₓ, ← add_tsub_cancel_of_le (le_of_not_gtₓ h), ← sm]
    

theorem mkpair_unpair' {n a b} (H : unpair n = (a, b)) : mkpair a b = n := by
  simpa [← H] using mkpair_unpair n

@[simp]
theorem unpair_mkpair (a b : ℕ) : unpair (mkpair a b) = (a, b) := by
  dunfold mkpair
  split_ifs
  · show unpair (b * b + a) = (a, b)
    have be : sqrt (b * b + a) = b := sqrt_add_eq _ (le_transₓ (le_of_ltₓ h) (Nat.le_add_leftₓ _ _))
    simp [← unpair, ← be, ← add_tsub_cancel_right, ← h]
    
  · show unpair (a * a + a + b) = (a, b)
    have ae : sqrt (a * a + (a + b)) = a := by
      rw [sqrt_add_eq]
      exact add_le_add_left (le_of_not_gtₓ h) _
    simp [← unpair, ← ae, ← Nat.not_lt_zeroₓ, ← add_assocₓ]
    

/-- An equivalence between `ℕ × ℕ` and `ℕ`. -/
@[simps (config := { fullyApplied := false })]
def mkpairEquiv : ℕ × ℕ ≃ ℕ :=
  ⟨uncurry mkpair, unpair, fun ⟨a, b⟩ => unpair_mkpair a b, mkpair_unpair⟩

theorem surjective_unpair : Surjective unpair :=
  mkpairEquiv.symm.Surjective

@[simp]
theorem mkpair_eq_mkpair {a b c d : ℕ} : mkpair a b = mkpair c d ↔ a = c ∧ b = d :=
  mkpairEquiv.Injective.eq_iff.trans (@Prod.ext_iff ℕ ℕ (a, b) (c, d))

theorem unpair_lt {n : ℕ} (n1 : 1 ≤ n) : (unpair n).1 < n := by
  let s := sqrt n
  simp [← unpair]
  change sqrt n with s
  by_cases' h : n - s * s < s <;> simp [← h]
  · exact lt_of_lt_of_leₓ h (sqrt_le_self _)
    
  · simp at h
    have s0 : 0 < s := sqrt_pos.2 n1
    exact lt_of_le_of_ltₓ h (tsub_lt_self n1 (mul_pos s0 s0))
    

@[simp]
theorem unpair_zero : unpair 0 = 0 := by
  rw [unpair]
  simp

theorem unpair_left_le : ∀ n : ℕ, (unpair n).1 ≤ n
  | 0 => by
    simp
  | n + 1 => le_of_ltₓ (unpair_lt (Nat.succ_posₓ _))

theorem left_le_mkpair (a b : ℕ) : a ≤ mkpair a b := by
  simpa using unpair_left_le (mkpair a b)

theorem right_le_mkpair (a b : ℕ) : b ≤ mkpair a b := by
  by_cases' h : a < b <;> simp [← mkpair, ← h]
  exact le_transₓ (le_mul_self _) (Nat.le_add_rightₓ _ _)

theorem unpair_right_le (n : ℕ) : (unpair n).2 ≤ n := by
  simpa using right_le_mkpair n.unpair.1 n.unpair.2

theorem mkpair_lt_mkpair_left {a₁ a₂} (b) (h : a₁ < a₂) : mkpair a₁ b < mkpair a₂ b := by
  by_cases' h₁ : a₁ < b <;> simp [← mkpair, ← h₁, ← add_assocₓ]
  · by_cases' h₂ : a₂ < b <;> simp [← mkpair, ← h₂, ← h]
    simp at h₂
    apply add_lt_add_of_le_of_lt
    exact mul_self_le_mul_self h₂
    exact lt_add_right _ _ _ h
    
  · simp at h₁
    simp [← not_lt_of_gtₓ (lt_of_le_of_ltₓ h₁ h)]
    apply add_lt_add
    exact mul_self_lt_mul_self h
    apply add_lt_add_right <;> assumption
    

theorem mkpair_lt_mkpair_right (a) {b₁ b₂} (h : b₁ < b₂) : mkpair a b₁ < mkpair a b₂ := by
  by_cases' h₁ : a < b₁ <;> simp [← mkpair, ← h₁, ← add_assocₓ]
  · simp [← mkpair, ← lt_transₓ h₁ h, ← h]
    exact mul_self_lt_mul_self h
    
  · by_cases' h₂ : a < b₂ <;> simp [← mkpair, ← h₂, ← h]
    simp at h₁
    rw [add_commₓ, add_commₓ _ a, add_assocₓ, add_lt_add_iff_left]
    rwa [add_commₓ, ← sqrt_lt, sqrt_add_eq]
    exact le_transₓ h₁ (Nat.le_add_leftₓ _ _)
    

end Nat

open Nat

section CompleteLattice

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem supr_unpair {α} [CompleteLattice α] (f : ℕ → ℕ → α) :
    (⨆ n : ℕ, f n.unpair.1 n.unpair.2) = ⨆ (i : ℕ) (j : ℕ), f i j := by
  rw [← (supr_prod : (⨆ i : ℕ × ℕ, f i.1 i.2) = _), ← nat.surjective_unpair.supr_comp]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem infi_unpair {α} [CompleteLattice α] (f : ℕ → ℕ → α) :
    (⨅ n : ℕ, f n.unpair.1 n.unpair.2) = ⨅ (i : ℕ) (j : ℕ), f i j :=
  supr_unpair (show ℕ → ℕ → αᵒᵈ from f)

end CompleteLattice

namespace Set

theorem Union_unpair_prod {α β} {s : ℕ → Set α} {t : ℕ → Set β} :
    (⋃ n : ℕ, s n.unpair.fst ×ˢ t n.unpair.snd) = (⋃ n, s n) ×ˢ ⋃ n, t n := by
  rw [← Union_prod]
  convert surjective_unpair.Union_comp _
  rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem Union_unpair {α} (f : ℕ → ℕ → Set α) : (⋃ n : ℕ, f n.unpair.1 n.unpair.2) = ⋃ (i : ℕ) (j : ℕ), f i j :=
  supr_unpair f

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem Inter_unpair {α} (f : ℕ → ℕ → Set α) : (⋂ n : ℕ, f n.unpair.1 n.unpair.2) = ⋂ (i : ℕ) (j : ℕ), f i j :=
  infi_unpair f

end Set

