/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathbin.Data.Zmod.Basic

/-!
# `ne_zero` typeclass

We create a typeclass `ne_zero n` which carries around the fact that `(n : R) ≠ 0`.

## Main declarations

* `ne_zero`: `n ≠ 0` as a typeclass.

-/


/-- A type-class version of `n ≠ 0`.  -/
class NeZero {R} [Zero R] (n : R) : Prop where
  out : n ≠ 0

theorem NeZero.ne {R} [Zero R] (n : R) [h : NeZero n] : n ≠ 0 :=
  h.out

theorem NeZero.ne' (n : ℕ) (R) [AddMonoidWithOneₓ R] [h : NeZero (n : R)] : (n : R) ≠ 0 :=
  h.out

theorem ne_zero_iff {R : Type _} [Zero R] {n : R} : NeZero n ↔ n ≠ 0 :=
  ⟨fun h => h.out, NeZero.mk⟩

theorem not_ne_zero {R : Type _} [Zero R] {n : R} : ¬NeZero n ↔ n = 0 := by
  simp [← ne_zero_iff]

namespace NeZero

variable {R S M F : Type _} {r : R} {x y : M} {n p : ℕ} {a : ℕ+}

instance pnat : NeZero (a : ℕ) :=
  ⟨a.ne_zero⟩

instance succ : NeZero (n + 1) :=
  ⟨n.succ_ne_zero⟩

theorem of_pos [Preorderₓ M] [Zero M] (h : 0 < x) : NeZero x :=
  ⟨h.ne'⟩

theorem of_gt [CanonicallyOrderedAddMonoid M] (h : x < y) : NeZero y :=
  of_pos <| pos_of_gt h

instance char_zero [NeZero n] [AddMonoidWithOneₓ M] [CharZero M] : NeZero (n : M) :=
  ⟨Nat.cast_ne_zero.mpr <| NeZero.ne n⟩

instance (priority := 100) invertible [MulZeroOneClassₓ M] [Nontrivial M] [Invertible x] : NeZero x :=
  ⟨nonzero_of_invertible x⟩

instance coe_trans [Zero M] [Coe R S] [CoeTₓ S M] [h : NeZero (r : M)] : NeZero ((r : S) : M) :=
  ⟨h.out⟩

theorem trans [Zero M] [Coe R S] [CoeTₓ S M] (h : NeZero ((r : S) : M)) : NeZero (r : M) :=
  ⟨h.out⟩

theorem of_map [Zero R] [Zero M] [ZeroHomClass F R M] (f : F) [NeZero (f r)] : NeZero r :=
  ⟨fun h =>
    ne (f r) <| by
      convert map_zero f⟩

theorem nat_of_ne_zero [Semiringₓ R] [Semiringₓ S] [RingHomClass F R S] (f : F) [hn : NeZero (n : S)] :
    NeZero (n : R) := by
  apply NeZero.of_map f
  simp [← hn]

theorem of_injective [Zero R] [h : NeZero r] [Zero M] [ZeroHomClass F R M] {f : F} (hf : Function.Injective f) :
    NeZero (f r) :=
  ⟨by
    rw [← map_zero f]
    exact hf.ne (Ne r)⟩

theorem nat_of_injective [NonAssocSemiringₓ M] [NonAssocSemiringₓ R] [h : NeZero (n : R)] [RingHomClass F R M] {f : F}
    (hf : Function.Injective f) : NeZero (n : M) :=
  ⟨fun h =>
    NeZero.ne' n R <|
      hf <| by
        simpa⟩

theorem pos (r : R) [CanonicallyOrderedAddMonoid R] [NeZero r] : 0 < r :=
  (zero_le r).lt_of_ne <| NeZero.out.symm

variable (R M)

theorem of_not_dvd [AddMonoidWithOneₓ M] [CharP M p] (h : ¬p ∣ n) : NeZero (n : M) :=
  ⟨(not_iff_not.mpr <| CharP.cast_eq_zero_iff M p n).mpr h⟩

theorem of_no_zero_smul_divisors (n : ℕ) [CommRingₓ R] [NeZero (n : R)] [Ringₓ M] [Nontrivial M] [Algebra R M]
    [NoZeroSmulDivisors R M] : NeZero (n : M) :=
  nat_of_injective <| NoZeroSmulDivisors.algebra_map_injective R M

theorem of_ne_zero_coe [AddMonoidWithOneₓ R] [h : NeZero (n : R)] : NeZero n :=
  ⟨by
    cases h
    rintro rfl
    · simpa using h
      ⟩

theorem not_char_dvd [AddMonoidWithOneₓ R] (p : ℕ) [CharP R p] (k : ℕ) [h : NeZero (k : R)] : ¬p ∣ k := by
  rwa [← not_iff_not.mpr <| CharP.cast_eq_zero_iff R p k, ← Ne.def, ← ne_zero_iff]

theorem pos_of_ne_zero_coe [AddMonoidWithOneₓ R] [NeZero (n : R)] : 0 < n :=
  (NeZero.of_ne_zero_coe R).out.bot_lt

end NeZero

theorem eq_zero_or_ne_zero {α} [Zero α] (a : α) : a = 0 ∨ NeZero a :=
  (eq_or_ne a 0).imp_right NeZero.mk

namespace Zmod

instance fintype' (n : ℕ) [NeZero n] : Fintype (Zmod n) :=
  @Zmod.fintype n ⟨NeZero.pos n⟩

end Zmod

