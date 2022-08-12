/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.GroupTheory.GroupAction.SubMulAction

/-!
# Pointwise monoid structures on sub_mul_action

This file provides `sub_mul_action.monoid` and weaker typeclasses, which show that `sub_mul_action`s
inherit the same pointwise multiplications as sets.

To match `submodule.semiring`, we do not put these in the `pointwise` locale.

-/


open Pointwise

variable {R M : Type _}

namespace SubMulAction

section One

variable [Monoidₓ R] [MulAction R M] [One M]

instance :
    One
      (SubMulAction R
        M) where one :=
    { Carrier := Set.Range fun r : R => r • (1 : M), smul_mem' := fun r m ⟨r', hr'⟩ => hr' ▸ ⟨r * r', mul_smul _ _ _⟩ }

theorem coe_one : ↑(1 : SubMulAction R M) = Set.Range fun r : R => r • (1 : M) :=
  rfl

@[simp]
theorem mem_one {x : M} : x ∈ (1 : SubMulAction R M) ↔ ∃ r : R, r • 1 = x :=
  Iff.rfl

theorem subset_coe_one : (1 : Set M) ⊆ (1 : SubMulAction R M) := fun x hx => ⟨1, (one_smul _ _).trans hx.symm⟩

end One

section Mul

variable [Monoidₓ R] [MulAction R M] [Mul M] [IsScalarTower R M M]

instance :
    Mul
      (SubMulAction R
        M) where mul := fun p q =>
    { Carrier := Set.Image2 (· * ·) p q,
      smul_mem' := fun r m ⟨m₁, m₂, hm₁, hm₂, h⟩ =>
        h ▸ smul_mul_assoc r m₁ m₂ ▸ Set.mul_mem_mul (p.smul_mem _ hm₁) hm₂ }

@[norm_cast]
theorem coe_mul (p q : SubMulAction R M) : ↑(p * q) = (p * q : Set M) :=
  rfl

theorem mem_mul {p q : SubMulAction R M} {x : M} : x ∈ p * q ↔ ∃ y z, y ∈ p ∧ z ∈ q ∧ y * z = x :=
  Set.mem_mul

end Mul

section MulOneClassₓ

variable [Monoidₓ R] [MulAction R M] [MulOneClassₓ M] [IsScalarTower R M M] [SmulCommClass R M M]

instance : MulOneClassₓ (SubMulAction R M) where
  mul := (· * ·)
  one := 1
  mul_one := fun a => by
    ext
    simp only [← mem_mul, ← mem_one, ← mul_smul_comm, ← exists_and_distrib_left, ← exists_exists_eq_and, ← mul_oneₓ]
    constructor
    · rintro ⟨y, hy, r, rfl⟩
      exact smul_mem _ _ hy
      
    · intro hx
      exact ⟨x, hx, 1, one_smul _ _⟩
      
  one_mul := fun a => by
    ext
    simp only [← mem_mul, ← mem_one, ← smul_mul_assoc, ← exists_and_distrib_left, ← exists_exists_eq_and, ← one_mulₓ]
    refine' ⟨_, fun hx => ⟨1, x, hx, one_smul _ _⟩⟩
    rintro ⟨r, y, hy, rfl⟩
    exact smul_mem _ _ hy

end MulOneClassₓ

section Semigroupₓ

variable [Monoidₓ R] [MulAction R M] [Semigroupₓ M] [IsScalarTower R M M]

instance : Semigroupₓ (SubMulAction R M) where
  mul := (· * ·)
  mul_assoc := fun a b c => SetLike.coe_injective (mul_assoc (_ : Set _) _ _)

end Semigroupₓ

section Monoidₓ

variable [Monoidₓ R] [MulAction R M] [Monoidₓ M] [IsScalarTower R M M] [SmulCommClass R M M]

instance : Monoidₓ (SubMulAction R M) :=
  { SubMulAction.semigroup, SubMulAction.mulOneClass with mul := (· * ·), one := 1 }

theorem coe_pow (p : SubMulAction R M) : ∀ {n : ℕ} (hn : n ≠ 0), ↑(p ^ n) = (p ^ n : Set M)
  | 0, hn => (hn rfl).elim
  | 1, hn => by
    rw [pow_oneₓ, pow_oneₓ]
  | n + 2, hn => by
    rw [pow_succₓ _ (n + 1), pow_succₓ _ (n + 1), coe_mul, coe_pow n.succ_ne_zero]

theorem subset_coe_pow (p : SubMulAction R M) : ∀ {n : ℕ}, (p ^ n : Set M) ⊆ ↑(p ^ n)
  | 0 => by
    rw [pow_zeroₓ, pow_zeroₓ]
    exact subset_coe_one
  | n + 1 => (coe_pow p n.succ_ne_zero).Superset

end Monoidₓ

end SubMulAction

