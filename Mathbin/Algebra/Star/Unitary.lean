/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Frédéric Dupuis
-/
import Mathbin.Algebra.Star.Basic
import Mathbin.GroupTheory.Submonoid.Membership

/-!
# Unitary elements of a star monoid

This file defines `unitary R`, where `R` is a star monoid, as the submonoid made of the elements
that satisfy `star U * U = 1` and `U * star U = 1`, and these form a group.
This includes, for instance, unitary operators on Hilbert spaces.

See also `matrix.unitary_group` for specializations to `unitary (matrix n n R)`.

## Tags

unitary
-/


/-- In a *-monoid, `unitary R` is the submonoid consisting of all the elements `U` of
`R` such that `star U * U = 1` and `U * star U = 1`.
-/
def unitary (R : Type _) [Monoidₓ R] [StarSemigroup R] : Submonoid R where
  Carrier := { U | star U * U = 1 ∧ U * star U = 1 }
  one_mem' := by
    simp only [← mul_oneₓ, ← and_selfₓ, ← Set.mem_set_of_eq, ← star_one]
  mul_mem' := fun U B ⟨hA₁, hA₂⟩ ⟨hB₁, hB₂⟩ => by
    refine' ⟨_, _⟩
    · calc star (U * B) * (U * B) = star B * star U * U * B := by
          simp only [← mul_assoc, ← star_mul]_ = star B * (star U * U) * B := by
          rw [← mul_assoc]_ = 1 := by
          rw [hA₁, mul_oneₓ, hB₁]
      
    · calc U * B * star (U * B) = U * B * (star B * star U) := by
          rw [star_mul]_ = U * (B * star B) * star U := by
          simp_rw [← mul_assoc]_ = 1 := by
          rw [hB₂, mul_oneₓ, hA₂]
      

variable {R : Type _}

namespace unitary

section Monoidₓ

variable [Monoidₓ R] [StarSemigroup R]

theorem mem_iff {U : R} : U ∈ unitary R ↔ star U * U = 1 ∧ U * star U = 1 :=
  Iff.rfl

@[simp]
theorem star_mul_self_of_mem {U : R} (hU : U ∈ unitary R) : star U * U = 1 :=
  hU.1

@[simp]
theorem mul_star_self_of_mem {U : R} (hU : U ∈ unitary R) : U * star U = 1 :=
  hU.2

theorem star_mem {U : R} (hU : U ∈ unitary R) : star U ∈ unitary R :=
  ⟨by
    rw [star_star, mul_star_self_of_mem hU], by
    rw [star_star, star_mul_self_of_mem hU]⟩

@[simp]
theorem star_mem_iff {U : R} : star U ∈ unitary R ↔ U ∈ unitary R :=
  ⟨fun h => star_star U ▸ star_mem h, star_mem⟩

instance : HasStar (unitary R) :=
  ⟨fun U => ⟨star U, star_mem U.Prop⟩⟩

@[simp, norm_cast]
theorem coe_star {U : unitary R} : ↑(star U) = (star U : R) :=
  rfl

theorem coe_star_mul_self (U : unitary R) : (star U : R) * U = 1 :=
  star_mul_self_of_mem U.Prop

theorem coe_mul_star_self (U : unitary R) : (U : R) * star U = 1 :=
  mul_star_self_of_mem U.Prop

@[simp]
theorem star_mul_self (U : unitary R) : star U * U = 1 :=
  Subtype.ext <| coe_star_mul_self U

@[simp]
theorem mul_star_self (U : unitary R) : U * star U = 1 :=
  Subtype.ext <| coe_mul_star_self U

instance : Groupₓ (unitary R) :=
  { Submonoid.toMonoid _ with inv := star, mul_left_inv := star_mul_self }

instance : HasInvolutiveStar (unitary R) :=
  ⟨fun _ => by
    ext
    simp only [← coe_star, ← star_star]⟩

instance : StarSemigroup (unitary R) :=
  ⟨fun _ _ => by
    ext
    simp only [← coe_star, ← Submonoid.coe_mul, ← star_mul]⟩

instance : Inhabited (unitary R) :=
  ⟨1⟩

theorem star_eq_inv (U : unitary R) : star U = U⁻¹ :=
  rfl

theorem star_eq_inv' : (star : unitary R → unitary R) = Inv.inv :=
  rfl

/-- The unitary elements embed into the units. -/
@[simps]
def toUnits : unitary R →* Rˣ where
  toFun := fun x => ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' := fun x y => Units.ext rfl

theorem to_units_injective : Function.Injective (toUnits : unitary R → Rˣ) := fun x y h =>
  Subtype.ext <| Units.ext_iff.mp h

end Monoidₓ

section CommMonoidₓ

variable [CommMonoidₓ R] [StarSemigroup R]

instance : CommGroupₓ (unitary R) :=
  { unitary.group, Submonoid.toCommMonoid _ with }

theorem mem_iff_star_mul_self {U : R} : U ∈ unitary R ↔ star U * U = 1 :=
  mem_iff.trans <| and_iff_left_of_imp fun h => mul_comm (star U) U ▸ h

theorem mem_iff_self_mul_star {U : R} : U ∈ unitary R ↔ U * star U = 1 :=
  mem_iff.trans <| and_iff_right_of_imp fun h => mul_comm U (star U) ▸ h

end CommMonoidₓ

section GroupWithZeroₓ

variable [GroupWithZeroₓ R] [StarSemigroup R]

@[norm_cast]
theorem coe_inv (U : unitary R) : ↑U⁻¹ = (U⁻¹ : R) :=
  eq_inv_of_mul_eq_one_right <| coe_mul_star_self _

@[norm_cast]
theorem coe_div (U₁ U₂ : unitary R) : ↑(U₁ / U₂) = (U₁ / U₂ : R) := by
  simp only [← div_eq_mul_inv, ← coe_inv, ← Submonoid.coe_mul]

@[norm_cast]
theorem coe_zpow (U : unitary R) (z : ℤ) : ↑(U ^ z) = (U ^ z : R) := by
  induction z
  · simp [← SubmonoidClass.coe_pow]
    
  · simp [← coe_inv]
    

end GroupWithZeroₓ

section Ringₓ

variable [Ringₓ R] [StarRing R]

instance :
    Neg (unitary R) where neg := fun U =>
    ⟨-U, by
      simp_rw [mem_iff, star_neg, neg_mul_neg]
      exact U.prop⟩

@[norm_cast]
theorem coe_neg (U : unitary R) : ↑(-U) = (-U : R) :=
  rfl

instance : HasDistribNeg (unitary R) :=
  Subtype.coe_injective.HasDistribNeg _ coe_neg (unitary R).coe_mul

end Ringₓ

end unitary

