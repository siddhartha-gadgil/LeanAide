/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Int.Basic
import Mathbin.Data.Nat.Cast
import Mathbin.Tactic.PiInstances

/-!
# Cast of integers (additional theorems)

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`int.cast`).

## Main declarations

* `cast_add_hom`: `cast` bundled as an `add_monoid_hom`.
* `cast_ring_hom`: `cast` bundled as a `ring_hom`.
-/


open Nat

namespace Int

/-- Coercion `ℕ → ℤ` as a `ring_hom`. -/
def ofNatHom : ℕ →+* ℤ :=
  ⟨coe, rfl, Int.of_nat_mul, rfl, Int.of_nat_add⟩

section cast

variable {α : Type _}

@[simp, norm_cast]
theorem cast_mul [NonAssocRing α] : ∀ m n, ((m * n : ℤ) : α) = m * n := fun m =>
  Int.inductionOn' m 0
    (by
      simp )
    (fun k _ ih n => by
      simp [← add_mulₓ, ← ih])
    fun k _ ih n => by
    simp [← sub_mul, ← ih]

@[simp, norm_cast]
theorem cast_ite [AddGroupWithOneₓ α] (P : Prop) [Decidable P] (m n : ℤ) : ((ite P m n : ℤ) : α) = ite P m n :=
  apply_ite _ _ _ _

/-- `coe : ℤ → α` as an `add_monoid_hom`. -/
def castAddHom (α : Type _) [AddGroupWithOneₓ α] : ℤ →+ α :=
  ⟨coe, cast_zeroₓ, cast_add⟩

@[simp]
theorem coe_cast_add_hom [AddGroupWithOneₓ α] : ⇑(castAddHom α) = coe :=
  rfl

/-- `coe : ℤ → α` as a `ring_hom`. -/
def castRingHom (α : Type _) [NonAssocRing α] : ℤ →+* α :=
  ⟨coe, cast_oneₓ, cast_mul, cast_zeroₓ, cast_add⟩

@[simp]
theorem coe_cast_ring_hom [NonAssocRing α] : ⇑(castRingHom α) = coe :=
  rfl

theorem cast_commute [NonAssocRing α] : ∀ (m : ℤ) (x : α), Commute (↑m) x
  | (n : ℕ), x => by
    simpa using n.cast_commute x
  | -[1+ n], x => by
    simpa only [← cast_neg_succ_of_nat, ← Commute.neg_left_iff, ← Commute.neg_right_iff] using (n + 1).cast_commute (-x)

theorem cast_comm [NonAssocRing α] (m : ℤ) (x : α) : (m : α) * x = x * m :=
  (cast_commute m x).Eq

theorem commute_cast [NonAssocRing α] (x : α) (m : ℤ) : Commute x m :=
  (m.cast_commute x).symm

theorem cast_mono [OrderedRing α] : Monotone (coe : ℤ → α) := by
  intro m n h
  rw [← sub_nonneg] at h
  lift n - m to ℕ using h with k
  rw [← sub_nonneg, ← cast_sub, ← h_1, cast_coe_nat]
  exact k.cast_nonneg

@[simp]
theorem cast_nonneg [OrderedRing α] [Nontrivial α] : ∀ {n : ℤ}, (0 : α) ≤ n ↔ 0 ≤ n
  | (n : ℕ) => by
    simp
  | -[1+ n] => by
    have : -(n : α) < 1 :=
      lt_of_le_of_ltₓ
        (by
          simp )
        zero_lt_one
    simpa [← (neg_succ_lt_zero n).not_le, sub_eq_add_neg, ← le_neg] using this.not_le

@[simp, norm_cast]
theorem cast_le [OrderedRing α] [Nontrivial α] {m n : ℤ} : (m : α) ≤ n ↔ m ≤ n := by
  rw [← sub_nonneg, ← cast_sub, cast_nonneg, sub_nonneg]

theorem cast_strict_mono [OrderedRing α] [Nontrivial α] : StrictMono (coe : ℤ → α) :=
  strict_mono_of_le_iff_le fun m n => cast_le.symm

@[simp, norm_cast]
theorem cast_lt [OrderedRing α] [Nontrivial α] {m n : ℤ} : (m : α) < n ↔ m < n :=
  cast_strict_mono.lt_iff_lt

@[simp]
theorem cast_nonpos [OrderedRing α] [Nontrivial α] {n : ℤ} : (n : α) ≤ 0 ↔ n ≤ 0 := by
  rw [← cast_zero, cast_le]

@[simp]
theorem cast_pos [OrderedRing α] [Nontrivial α] {n : ℤ} : (0 : α) < n ↔ 0 < n := by
  rw [← cast_zero, cast_lt]

@[simp]
theorem cast_lt_zero [OrderedRing α] [Nontrivial α] {n : ℤ} : (n : α) < 0 ↔ n < 0 := by
  rw [← cast_zero, cast_lt]

section LinearOrderedRing

variable [LinearOrderedRing α] {a b : ℤ} (n : ℤ)

@[simp, norm_cast]
theorem cast_min : (↑(min a b) : α) = min a b :=
  Monotone.map_min cast_mono

@[simp, norm_cast]
theorem cast_max : (↑(max a b) : α) = max a b :=
  Monotone.map_max cast_mono

@[simp, norm_cast]
theorem cast_abs : ((abs a : ℤ) : α) = abs a := by
  simp [← abs_eq_max_neg]

theorem cast_one_le_of_pos (h : 0 < a) : (1 : α) ≤ a := by
  exact_mod_cast Int.add_one_le_of_ltₓ h

theorem cast_le_neg_one_of_neg (h : a < 0) : (a : α) ≤ -1 := by
  rw [← Int.cast_oneₓ, ← Int.cast_neg, cast_le]
  exact Int.le_sub_one_of_ltₓ h

theorem nneg_mul_add_sq_of_abs_le_one {x : α} (hx : abs x ≤ 1) : (0 : α) ≤ n * x + n * n := by
  have hnx : 0 < n → 0 ≤ x + n := fun hn => by
    convert add_le_add (neg_le_of_abs_le hx) (cast_one_le_of_pos hn)
    rw [add_left_negₓ]
  have hnx' : n < 0 → x + n ≤ 0 := fun hn => by
    convert add_le_add (le_of_abs_le hx) (cast_le_neg_one_of_neg hn)
    rw [add_right_negₓ]
  rw [← mul_addₓ, mul_nonneg_iff]
  rcases lt_trichotomyₓ n 0 with (h | rfl | h)
  · exact
      Or.inr
        ⟨by
          exact_mod_cast h.le, hnx' h⟩
    
  · simp [← le_totalₓ 0 x]
    
  · exact
      Or.inl
        ⟨by
          exact_mod_cast h.le, hnx h⟩
    

theorem cast_nat_abs : (n.natAbs : α) = abs n := by
  cases n
  · simp
    
  · simp only [← Int.natAbs, ← Int.cast_neg_succ_of_nat, ← abs_neg, Nat.cast_succₓ, ← Nat.abs_cast]
    

end LinearOrderedRing

theorem coe_int_dvd [CommRingₓ α] (m n : ℤ) (h : m ∣ n) : (m : α) ∣ (n : α) :=
  RingHom.map_dvd (Int.castRingHom α) h

end cast

end Int

namespace Prod

variable {α : Type _} {β : Type _} [AddGroupWithOneₓ α] [AddGroupWithOneₓ β]

instance : AddGroupWithOneₓ (α × β) :=
  { Prod.addMonoidWithOne, Prod.addGroup with intCast := fun n => (n, n),
    int_cast_of_nat := fun _ => by
      simp <;> rfl,
    int_cast_neg_succ_of_nat := fun _ => by
      simp <;> rfl }

@[simp]
theorem fst_int_cast (n : ℤ) : (n : α × β).fst = n :=
  rfl

@[simp]
theorem snd_int_cast (n : ℤ) : (n : α × β).snd = n :=
  rfl

end Prod

open Int

namespace AddMonoidHom

variable {A : Type _}

/-- Two additive monoid homomorphisms `f`, `g` from `ℤ` to an additive monoid are equal
if `f 1 = g 1`. -/
@[ext]
theorem ext_int [AddMonoidₓ A] {f g : ℤ →+ A} (h1 : f 1 = g 1) : f = g :=
  have : f.comp (Int.ofNatHom : ℕ →+ ℤ) = g.comp (Int.ofNatHom : ℕ →+ ℤ) := ext_nat' _ _ h1
  have : ∀ n : ℕ, f n = g n := ext_iff.1 this
  ext fun n => (Int.casesOn n this) fun n => eq_on_neg (this <| n + 1)

variable [AddGroupWithOneₓ A]

theorem eq_int_cast_hom (f : ℤ →+ A) (h1 : f 1 = 1) : f = Int.castAddHom A :=
  ext_int <| by
    simp [← h1]

theorem eq_int_cast (f : ℤ →+ A) (h1 : f 1 = 1) : ∀ n : ℤ, f n = n :=
  ext_iff.1 (f.eq_int_cast_hom h1)

end AddMonoidHom

@[simp]
theorem Int.cast_add_hom_int : Int.castAddHom ℤ = AddMonoidHom.id ℤ :=
  ((AddMonoidHom.id ℤ).eq_int_cast_hom rfl).symm

namespace MonoidHom

variable {M : Type _} [Monoidₓ M]

open Multiplicative

@[ext]
theorem ext_mint {f g : Multiplicative ℤ →* M} (h1 : f (ofAdd 1) = g (ofAdd 1)) : f = g :=
  MonoidHom.ext <| AddMonoidHom.ext_iff.mp <| @AddMonoidHom.ext_int _ _ f.toAdditive g.toAdditive h1

/-- If two `monoid_hom`s agree on `-1` and the naturals then they are equal. -/
@[ext]
theorem ext_int {f g : ℤ →* M} (h_neg_one : f (-1) = g (-1))
    (h_nat : f.comp Int.ofNatHom.toMonoidHom = g.comp Int.ofNatHom.toMonoidHom) : f = g := by
  ext (x | x)
  · exact (MonoidHom.congr_fun h_nat x : _)
    
  · rw [Int.neg_succ_of_nat_eq, ← neg_one_mul, f.map_mul, g.map_mul]
    congr 1
    exact_mod_cast (MonoidHom.congr_fun h_nat (x + 1) : _)
    

end MonoidHom

namespace MonoidWithZeroHom

variable {M : Type _} [MonoidWithZeroₓ M]

/-- If two `monoid_with_zero_hom`s agree on `-1` and the naturals then they are equal. -/
@[ext]
theorem ext_int {f g : ℤ →*₀ M} (h_neg_one : f (-1) = g (-1))
    (h_nat : f.comp Int.ofNatHom.toMonoidWithZeroHom = g.comp Int.ofNatHom.toMonoidWithZeroHom) : f = g :=
  to_monoid_hom_injective <| MonoidHom.ext_int h_neg_one <| MonoidHom.ext (congr_fun h_nat : _)

/-- If two `monoid_with_zero_hom`s agree on `-1` and the _positive_ naturals then they are equal. -/
theorem ext_int' {φ₁ φ₂ : ℤ →*₀ M} (h_neg_one : φ₁ (-1) = φ₂ (-1)) (h_pos : ∀ n : ℕ, 0 < n → φ₁ n = φ₂ n) : φ₁ = φ₂ :=
  ext_int h_neg_one <| ext_nat h_pos

end MonoidWithZeroHom

namespace RingHom

variable {α : Type _} {β : Type _} [NonAssocRing α] [NonAssocRing β]

@[simp]
theorem eq_int_cast (f : ℤ →+* α) (n : ℤ) : f n = n :=
  f.toAddMonoidHom.eq_int_cast f.map_one n

theorem eq_int_cast' (f : ℤ →+* α) : f = Int.castRingHom α :=
  RingHom.ext f.eq_int_cast

@[simp]
theorem map_int_cast (f : α →+* β) (n : ℤ) : f n = n :=
  (f.comp (Int.castRingHom α)).eq_int_cast n

theorem ext_int {R : Type _} [NonAssocSemiringₓ R] (f g : ℤ →+* R) : f = g :=
  coe_add_monoid_hom_injective <| AddMonoidHom.ext_int <| f.map_one.trans g.map_one.symm

instance Int.subsingleton_ring_hom {R : Type _} [NonAssocSemiringₓ R] : Subsingleton (ℤ →+* R) :=
  ⟨RingHom.ext_int⟩

end RingHom

@[simp, norm_cast]
theorem Int.cast_id (n : ℤ) : ↑n = n :=
  ((RingHom.id ℤ).eq_int_cast n).symm

@[simp]
theorem Int.cast_ring_hom_int : Int.castRingHom ℤ = RingHom.id ℤ :=
  (RingHom.id ℤ).eq_int_cast'.symm

namespace Pi

variable {α : Type _} {β : α → Type _} [∀ a, HasIntCast (β a)]

instance : HasIntCast (∀ a, β a) := by
  refine_struct { .. } <;>
    run_tac
      tactic.pi_instance_derive_field

theorem int_apply (n : ℤ) (a : α) : (n : ∀ a, β a) a = n :=
  rfl

@[simp]
theorem coe_int (n : ℤ) : (n : ∀ a, β a) = fun _ => n :=
  rfl

end Pi

namespace Pi

variable {α : Type _} {β : α → Type _} [∀ a, AddGroupWithOneₓ (β a)]

instance : AddGroupWithOneₓ (∀ a, β a) := by
  refine_struct { .. } <;>
    run_tac
      tactic.pi_instance_derive_field

end Pi

namespace MulOpposite

variable {α : Type _} [AddGroupWithOneₓ α]

@[simp, norm_cast]
theorem op_int_cast (z : ℤ) : op (z : α) = z :=
  rfl

@[simp, norm_cast]
theorem unop_int_cast (n : ℤ) : unop (n : αᵐᵒᵖ) = n :=
  rfl

end MulOpposite

