/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

/-!
# More `char` instances

This file provides a `linear_order` instance on `char`. `char` is the type of Unicode scalar values.
-/


instance : LinearOrderₓ Charₓ :=
  { Charₓ.hasLe, Charₓ.hasLt with le_refl := fun a => @le_reflₓ ℕ _ _, le_trans := fun a b c => @le_transₓ ℕ _ _ _ _,
    le_antisymm := fun a b h₁ h₂ => Charₓ.eq_of_veq <| le_antisymmₓ h₁ h₂, le_total := fun a b => @le_totalₓ ℕ _ _ _,
    lt_iff_le_not_le := fun a b => @lt_iff_le_not_leₓ ℕ _ _ _, decidableLe := Charₓ.decidableLe,
    DecidableEq := Charₓ.decidableEq, decidableLt := Charₓ.decidableLt }

theorem Charₓ.of_nat_to_nat {c : Charₓ} (h : IsValidChar c.toNat) : Charₓ.ofNat c.toNat = c := by
  rw [Charₓ.ofNat, dif_pos h]
  cases c
  simp [← Charₓ.toNat]

