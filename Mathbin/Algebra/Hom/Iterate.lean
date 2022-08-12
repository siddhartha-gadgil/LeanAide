/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Algebra.GroupPower.Basic
import Mathbin.Logic.Function.Iterate
import Mathbin.GroupTheory.Perm.Basic
import Mathbin.GroupTheory.GroupAction.Opposite

/-!
# Iterates of monoid and ring homomorphisms

Iterate of a monoid/ring homomorphism is a monoid/ring homomorphism but it has a wrong type, so Lean
can't apply lemmas like `monoid_hom.map_one` to `f^[n] 1`. Though it is possible to define
a monoid structure on the endomorphisms, quite often we do not want to convert from
`M →* M` to `monoid.End M` and from `f^[n]` to `f^n` just to apply a simple lemma.

So, we restate standard `*_hom.map_*` lemmas under names `*_hom.iterate_map_*`.

We also prove formulas for iterates of add/mul left/right.

## Tags

homomorphism, iterate
-/


open Function

variable {M : Type _} {N : Type _} {G : Type _} {H : Type _}

/-- An auxiliary lemma that can be used to prove `⇑(f ^ n) = (⇑f^[n])`. -/
theorem hom_coe_pow {F : Type _} [Monoidₓ F] (c : F → M → M) (h1 : c 1 = id) (hmul : ∀ f g, c (f * g) = c f ∘ c g)
    (f : F) : ∀ n, c (f ^ n) = c f^[n]
  | 0 => by
    rw [pow_zeroₓ, h1]
    rfl
  | n + 1 => by
    rw [pow_succₓ, iterate_succ', hmul, hom_coe_pow]

namespace MonoidHom

section

variable [MulOneClassₓ M] [MulOneClassₓ N]

@[simp, to_additive]
theorem iterate_map_one (f : M →* M) (n : ℕ) : (f^[n]) 1 = 1 :=
  iterate_fixed f.map_one n

@[simp, to_additive]
theorem iterate_map_mul (f : M →* M) (n : ℕ) (x y) : (f^[n]) (x * y) = (f^[n]) x * (f^[n]) y :=
  Semiconj₂.iterate f.map_mul n x y

end

variable [Monoidₓ M] [Monoidₓ N] [Groupₓ G] [Groupₓ H]

@[simp, to_additive]
theorem iterate_map_inv (f : G →* G) (n : ℕ) (x) : (f^[n]) x⁻¹ = ((f^[n]) x)⁻¹ :=
  Commute.iterate_left f.map_inv n x

@[simp, to_additive]
theorem iterate_map_div (f : G →* G) (n : ℕ) (x y) : (f^[n]) (x / y) = (f^[n]) x / (f^[n]) y :=
  Semiconj₂.iterate f.map_div n x y

theorem iterate_map_pow (f : M →* M) (n : ℕ) (a) (m : ℕ) : (f^[n]) (a ^ m) = (f^[n]) a ^ m :=
  Commute.iterate_left (fun x => f.map_pow x m) n a

theorem iterate_map_zpow (f : G →* G) (n : ℕ) (a) (m : ℤ) : (f^[n]) (a ^ m) = (f^[n]) a ^ m :=
  Commute.iterate_left (fun x => f.map_zpow x m) n a

theorem coe_pow {M} [CommMonoidₓ M] (f : Monoidₓ.End M) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun f g => rfl) _ _

end MonoidHom

theorem Monoidₓ.End.coe_pow {M} [Monoidₓ M] (f : Monoidₓ.End M) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun f g => rfl) _ _

-- we define these manually so that we can pick a better argument order
namespace AddMonoidHom

variable [AddMonoidₓ M] [AddGroupₓ G]

theorem iterate_map_smul (f : M →+ M) (n m : ℕ) (x : M) : (f^[n]) (m • x) = m • (f^[n]) x :=
  f.toMultiplicative.iterate_map_pow n x m

attribute [to_additive, to_additive_reorder 5] MonoidHom.iterate_map_pow

theorem iterate_map_zsmul (f : G →+ G) (n : ℕ) (m : ℤ) (x : G) : (f^[n]) (m • x) = m • (f^[n]) x :=
  f.toMultiplicative.iterate_map_zpow n x m

attribute [to_additive, to_additive_reorder 5] MonoidHom.iterate_map_zpow

end AddMonoidHom

theorem AddMonoidₓ.End.coe_pow {A} [AddMonoidₓ A] (f : AddMonoidₓ.End A) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun f g => rfl) _ _

namespace RingHom

section Semiringₓ

variable {R : Type _} [Semiringₓ R] (f : R →+* R) (n : ℕ) (x y : R)

theorem coe_pow (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun f g => rfl) f n

theorem iterate_map_one : (f^[n]) 1 = 1 :=
  f.toMonoidHom.iterate_map_one n

theorem iterate_map_zero : (f^[n]) 0 = 0 :=
  f.toAddMonoidHom.iterate_map_zero n

theorem iterate_map_add : (f^[n]) (x + y) = (f^[n]) x + (f^[n]) y :=
  f.toAddMonoidHom.iterate_map_add n x y

theorem iterate_map_mul : (f^[n]) (x * y) = (f^[n]) x * (f^[n]) y :=
  f.toMonoidHom.iterate_map_mul n x y

theorem iterate_map_pow (a) (n m : ℕ) : (f^[n]) (a ^ m) = (f^[n]) a ^ m :=
  f.toMonoidHom.iterate_map_pow n a m

theorem iterate_map_smul (n m : ℕ) (x : R) : (f^[n]) (m • x) = m • (f^[n]) x :=
  f.toAddMonoidHom.iterate_map_smul n m x

end Semiringₓ

variable {R : Type _} [Ringₓ R] (f : R →+* R) (n : ℕ) (x y : R)

theorem iterate_map_sub : (f^[n]) (x - y) = (f^[n]) x - (f^[n]) y :=
  f.toAddMonoidHom.iterate_map_sub n x y

theorem iterate_map_neg : (f^[n]) (-x) = -(f^[n]) x :=
  f.toAddMonoidHom.iterate_map_neg n x

theorem iterate_map_zsmul (n : ℕ) (m : ℤ) (x : R) : (f^[n]) (m • x) = m • (f^[n]) x :=
  f.toAddMonoidHom.iterate_map_zsmul n m x

end RingHom

theorem Equivₓ.Perm.coe_pow {α : Type _} (f : Equivₓ.Perm α) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ => rfl) _ _

--what should be the namespace for this section?
section Monoidₓ

variable [Monoidₓ G] (a : G) (n : ℕ)

@[simp, to_additive]
theorem smul_iterate [MulAction G H] : ((· • ·) a : H → H)^[n] = (· • ·) (a ^ n) :=
  funext fun b =>
    Nat.recOn n
      (by
        rw [iterate_zero, id.def, pow_zeroₓ, one_smul])
      fun n ih => by
      rw [iterate_succ', comp_app, ih, pow_succₓ, mul_smul]

@[simp, to_additive]
theorem mul_left_iterate : (· * ·) a^[n] = (· * ·) (a ^ n) :=
  smul_iterate a n

@[simp, to_additive]
theorem mul_right_iterate : (· * a)^[n] = (· * a ^ n) :=
  smul_iterate (MulOpposite.op a) n

@[to_additive]
theorem mul_right_iterate_apply_one : ((· * a)^[n]) 1 = a ^ n := by
  simp [← mul_right_iterate]

end Monoidₓ

section Semigroupₓ

variable [Semigroupₓ G] {a b c : G}

@[to_additive]
theorem SemiconjBy.function_semiconj_mul_left (h : SemiconjBy a b c) :
    Function.Semiconj ((· * ·) a) ((· * ·) b) ((· * ·) c) := fun j => by
  rw [← mul_assoc, h.eq, mul_assoc]

@[to_additive]
theorem Commute.function_commute_mul_left (h : Commute a b) : Function.Commute ((· * ·) a) ((· * ·) b) :=
  SemiconjBy.function_semiconj_mul_left h

@[to_additive]
theorem SemiconjBy.function_semiconj_mul_right_swap (h : SemiconjBy a b c) :
    Function.Semiconj (· * a) (· * c) (· * b) := fun j => by
  simp_rw [mul_assoc, ← h.eq]

@[to_additive]
theorem Commute.function_commute_mul_right (h : Commute a b) : Function.Commute (· * a) (· * b) :=
  SemiconjBy.function_semiconj_mul_right_swap h

end Semigroupₓ

