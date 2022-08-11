/-
Copyright (c) 2020 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import Mathbin.Data.Fintype.Card
import Mathbin.Data.Zmod.Basic
import Mathbin.GroupTheory.Exponent
import Mathbin.Data.Int.Parity

/-!
# Dihedral Groups

We define the dihedral groups `dihedral_group n`, with elements `r i` and `sr i` for `i : zmod n`.

For `n ≠ 0`, `dihedral_group n` represents the symmetry group of the regular `n`-gon. `r i`
represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of the
`n`-gon. `dihedral_group 0` corresponds to the infinite dihedral group.
-/


/-- For `n ≠ 0`, `dihedral_group n` represents the symmetry group of the regular `n`-gon.
`r i` represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of
the `n`-gon. `dihedral_group 0` corresponds to the infinite dihedral group.
-/
inductive DihedralGroup (n : ℕ) : Type
  | r : Zmod n → DihedralGroup
  | sr : Zmod n → DihedralGroup
  deriving DecidableEq

namespace DihedralGroup

variable {n : ℕ}

/-- Multiplication of the dihedral group.
-/
private def mul : DihedralGroup n → DihedralGroup n → DihedralGroup n
  | r i, r j => r (i + j)
  | r i, sr j => sr (j - i)
  | sr i, r j => sr (i + j)
  | sr i, sr j => r (j - i)

/-- The identity `1` is the rotation by `0`.
-/
private def one : DihedralGroup n :=
  r 0

instance : Inhabited (DihedralGroup n) :=
  ⟨one⟩

/-- The inverse of a an element of the dihedral group.
-/
private def inv : DihedralGroup n → DihedralGroup n
  | r i => r (-i)
  | sr i => sr i

/-- The group structure on `dihedral_group n`.
-/
instance : Groupₓ (DihedralGroup n) where
  mul := mul
  mul_assoc := by
    rintro (a | a) (b | b) (c | c) <;> simp only [← mul] <;> ring
  one := one
  one_mul := by
    rintro (a | a)
    exact congr_arg r (zero_addₓ a)
    exact congr_arg sr (sub_zero a)
  mul_one := by
    rintro (a | a)
    exact congr_arg r (add_zeroₓ a)
    exact congr_arg sr (add_zeroₓ a)
  inv := inv
  mul_left_inv := by
    rintro (a | a)
    exact congr_arg r (neg_add_selfₓ a)
    exact congr_arg r (sub_self a)

@[simp]
theorem r_mul_r (i j : Zmod n) : r i * r j = r (i + j) :=
  rfl

@[simp]
theorem r_mul_sr (i j : Zmod n) : r i * sr j = sr (j - i) :=
  rfl

@[simp]
theorem sr_mul_r (i j : Zmod n) : sr i * r j = sr (i + j) :=
  rfl

@[simp]
theorem sr_mul_sr (i j : Zmod n) : sr i * sr j = r (j - i) :=
  rfl

theorem one_def : (1 : DihedralGroup n) = r 0 :=
  rfl

private def fintype_helper : Sum (Zmod n) (Zmod n) ≃ DihedralGroup n where
  invFun := fun i =>
    match i with
    | r j => Sum.inl j
    | sr j => Sum.inr j
  toFun := fun i =>
    match i with
    | Sum.inl j => r j
    | Sum.inr j => sr j
  left_inv := by
    rintro (x | x) <;> rfl
  right_inv := by
    rintro (x | x) <;> rfl

/-- If `0 < n`, then `dihedral_group n` is a finite group.
-/
instance [Fact (0 < n)] : Fintype (DihedralGroup n) :=
  Fintype.ofEquiv _ fintypeHelper

instance : Nontrivial (DihedralGroup n) :=
  ⟨⟨r 0, sr 0, by
      decide⟩⟩

/-- If `0 < n`, then `dihedral_group n` has `2n` elements.
-/
theorem card [Fact (0 < n)] : Fintype.card (DihedralGroup n) = 2 * n := by
  rw [← fintype.card_eq.mpr ⟨fintype_helper⟩, Fintype.card_sum, Zmod.card, two_mul]

@[simp]
theorem r_one_pow (k : ℕ) : (r 1 : DihedralGroup n) ^ k = r k := by
  induction' k with k IH
  · rw [Nat.cast_zeroₓ]
    rfl
    
  · rw [pow_succₓ, IH, r_mul_r]
    congr 1
    norm_cast
    rw [Nat.one_add]
    

@[simp]
theorem r_one_pow_n : r (1 : Zmod n) ^ n = 1 := by
  rw [r_one_pow, one_def]
  congr 1
  exact Zmod.nat_cast_self _

@[simp]
theorem sr_mul_self (i : Zmod n) : sr i * sr i = 1 := by
  rw [sr_mul_sr, sub_self, one_def]

/-- If `0 < n`, then `sr i` has order 2.
-/
@[simp]
theorem order_of_sr (i : Zmod n) : orderOf (sr i) = 2 := by
  rw [order_of_eq_prime _ _]
  · exact ⟨Nat.prime_two⟩
    
  rw [sq, sr_mul_self]
  decide

/-- If `0 < n`, then `r 1` has order `n`.
-/
@[simp]
theorem order_of_r_one : orderOf (r 1 : DihedralGroup n) = n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · rw [order_of_eq_zero_iff']
    intro n hn
    rw [r_one_pow, one_def]
    apply mt r.inj
    simpa using hn.ne'
    
  · have := Fact.mk hn
    apply (Nat.le_of_dvdₓ hn <| order_of_dvd_of_pow_eq_one <| @r_one_pow_n n).lt_or_eq.resolve_left
    intro h
    have h1 : (r 1 : DihedralGroup n) ^ orderOf (r 1) = 1 := pow_order_of_eq_one _
    rw [r_one_pow] at h1
    injection h1 with h2
    rw [← Zmod.val_eq_zero, Zmod.val_nat_cast, Nat.mod_eq_of_ltₓ h] at h2
    exact absurd h2.symm (order_of_pos _).Ne
    

/-- If `0 < n`, then `i : zmod n` has order `n / gcd n i`.
-/
theorem order_of_r [Fact (0 < n)] (i : Zmod n) : orderOf (r i) = n / Nat.gcdₓ n i.val := by
  conv_lhs => rw [← Zmod.nat_cast_zmod_val i]
  rw [← r_one_pow, order_of_pow, order_of_r_one]

theorem exponent : Monoidₓ.exponent (DihedralGroup n) = lcm n 2 := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · exact Monoidₓ.exponent_eq_zero_of_order_zero order_of_r_one
    
  have := Fact.mk hn
  apply Nat.dvd_antisymm
  · apply Monoidₓ.exponent_dvd_of_forall_pow_eq_one
    rintro (m | m)
    · rw [← order_of_dvd_iff_pow_eq_one, order_of_r]
      refine' Nat.dvd_trans ⟨gcd n m.val, _⟩ (dvd_lcm_left n 2)
      · exact (Nat.div_mul_cancelₓ (Nat.gcd_dvd_leftₓ n m.val)).symm
        
      
    · rw [← order_of_dvd_iff_pow_eq_one, order_of_sr]
      exact dvd_lcm_right n 2
      
    
  · apply lcm_dvd
    · convert Monoidₓ.order_dvd_exponent (r 1)
      exact order_of_r_one.symm
      
    · convert Monoidₓ.order_dvd_exponent (sr 0)
      exact (order_of_sr 0).symm
      
    

end DihedralGroup

