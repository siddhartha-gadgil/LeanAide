/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathbin.Data.Int.Modeq

/-!
# Definition of `zmod n` + basic results.

This file provides the basic details of `zmod n`, including its commutative ring structure.

## Implementation details

This used to be inlined into data/zmod/basic.lean. This file imports `char_p/basic`, which is an
issue; all `char_p` instances create an `algebra (zmod p) R` instance; however, this instance may
not be definitionally equal to other `algebra` instances (for example, `galois_field` also has an
`algebra` instance as it is defined as a `splitting_field`). The way to fix this is to use the
forgetful inheritance pattern, and make `char_p` carry the data of what the `smul` should be (so
for example, the `smul` on the `galois_field` `char_p` instance should be equal to the `smul` from
its `splitting_field` structure); there is only one possible `zmod p` algebra for any `p`, so this
is not an issue mathematically. For this to be possible, however, we need `char_p/basic` to be
able to import some part of `zmod`.

-/


namespace Finₓ

/-!
## Ring structure on `fin n`

We define a commutative ring structure on `fin n`, but we do not register it as instance.
Afterwords, when we define `zmod n` in terms of `fin n`, we use these definitions
to register the ring structure on `zmod n` as type class instance.
-/


open Nat.Modeq Int

/-- Multiplicative commutative semigroup structure on `fin (n+1)`. -/
instance (n : ℕ) : CommSemigroupₓ (Finₓ (n + 1)) :=
  { Finₓ.hasMul with
    mul_assoc := fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ =>
      Finₓ.eq_of_veq
        (calc
          a * b % (n + 1) * c ≡ a * b * c [MOD n + 1] := (Nat.mod_modeq _ _).mul_right _
          _ ≡ a * (b * c) [MOD n + 1] := by
            rw [mul_assoc]
          _ ≡ a * (b * c % (n + 1)) [MOD n + 1] := (Nat.mod_modeq _ _).symm.mul_left _
          ),
    mul_comm := fun ⟨a, _⟩ ⟨b, _⟩ =>
      Finₓ.eq_of_veq
        (show a * b % (n + 1) = b * a % (n + 1) by
          rw [mul_comm]) }

private theorem left_distrib_aux (n : ℕ) : ∀ a b c : Finₓ (n + 1), a * (b + c) = a * b + a * c :=
  fun ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ =>
  Finₓ.eq_of_veq
    (calc
      a * ((b + c) % (n + 1)) ≡ a * (b + c) [MOD n + 1] := (Nat.mod_modeq _ _).mul_left _
      _ ≡ a * b + a * c [MOD n + 1] := by
        rw [mul_addₓ]
      _ ≡ a * b % (n + 1) + a * c % (n + 1) [MOD n + 1] := (Nat.mod_modeq _ _).symm.add (Nat.mod_modeq _ _).symm
      )

/-- Commutative ring structure on `fin (n+1)`. -/
instance (n : ℕ) : CommRingₓ (Finₓ (n + 1)) :=
  { Finₓ.addMonoidWithOne, Finₓ.addCommGroup n, Finₓ.commSemigroup n with one_mul := Finₓ.one_mul,
    mul_one := Finₓ.mul_one, left_distrib := left_distrib_aux n,
    right_distrib := fun a b c => by
      rw [mul_comm, left_distrib_aux, mul_comm _ b, mul_comm] <;> rfl }

end Finₓ

/-- The integers modulo `n : ℕ`. -/
def Zmod : ℕ → Type
  | 0 => ℤ
  | n + 1 => Finₓ (n + 1)

instance Zmod.decidableEq : ∀ n : ℕ, DecidableEq (Zmod n)
  | 0 => Int.decidableEq
  | n + 1 => Finₓ.decidableEq _

instance Zmod.hasRepr : ∀ n : ℕ, HasRepr (Zmod n)
  | 0 => Int.hasRepr
  | n + 1 => Finₓ.hasRepr _

namespace Zmod

instance fintype : ∀ (n : ℕ) [Fact (0 < n)], Fintype (Zmod n)
  | 0, h => (lt_irreflₓ _ h.1).elim
  | n + 1, _ => Finₓ.fintype (n + 1)

instance infinite : Infinite (Zmod 0) :=
  Int.infinite

@[simp]
theorem card (n : ℕ) [Fintype (Zmod n)] : Fintype.card (Zmod n) = n := by
  cases n
  · exact (not_fintype (Zmod 0)).elim
    
  · convert Fintype.card_fin (n + 1)
    

/- We define each field by cases, to ensure that the eta-expanded `zmod.comm_ring` is defeq to the
original, this helps avoid diamonds with instances coming from classes extending `comm_ring` such as
field. -/
instance commRing (n : ℕ) : CommRingₓ (Zmod n) where
  add := Nat.casesOn n (@Add.add Int _) fun n => @Add.add (Finₓ n.succ) _
  add_assoc := Nat.casesOn n (@add_assocₓ Int _) fun n => @add_assocₓ (Finₓ n.succ) _
  zero := Nat.casesOn n (0 : Int) fun n => (0 : Finₓ n.succ)
  zero_add := Nat.casesOn n (@zero_addₓ Int _) fun n => @zero_addₓ (Finₓ n.succ) _
  add_zero := Nat.casesOn n (@add_zeroₓ Int _) fun n => @add_zeroₓ (Finₓ n.succ) _
  neg := Nat.casesOn n (@Neg.neg Int _) fun n => @Neg.neg (Finₓ n.succ) _
  sub := Nat.casesOn n (@Sub.sub Int _) fun n => @Sub.sub (Finₓ n.succ) _
  sub_eq_add_neg := Nat.casesOn n (@sub_eq_add_neg Int _) fun n => @sub_eq_add_neg (Finₓ n.succ) _
  zsmul := Nat.casesOn n (@CommRingₓ.zsmul Int _) fun n => @CommRingₓ.zsmul (Finₓ n.succ) _
  zsmul_zero' := Nat.casesOn n (@CommRingₓ.zsmul_zero' Int _) fun n => @CommRingₓ.zsmul_zero' (Finₓ n.succ) _
  zsmul_succ' := Nat.casesOn n (@CommRingₓ.zsmul_succ' Int _) fun n => @CommRingₓ.zsmul_succ' (Finₓ n.succ) _
  zsmul_neg' := Nat.casesOn n (@CommRingₓ.zsmul_neg' Int _) fun n => @CommRingₓ.zsmul_neg' (Finₓ n.succ) _
  nsmul := Nat.casesOn n (@CommRingₓ.nsmul Int _) fun n => @CommRingₓ.nsmul (Finₓ n.succ) _
  nsmul_zero' := Nat.casesOn n (@CommRingₓ.nsmul_zero' Int _) fun n => @CommRingₓ.nsmul_zero' (Finₓ n.succ) _
  nsmul_succ' := Nat.casesOn n (@CommRingₓ.nsmul_succ' Int _) fun n => @CommRingₓ.nsmul_succ' (Finₓ n.succ) _
  add_left_neg := by
    cases n
    exacts[@add_left_negₓ Int _, @add_left_negₓ (Finₓ n.succ) _]
  add_comm := Nat.casesOn n (@add_commₓ Int _) fun n => @add_commₓ (Finₓ n.succ) _
  mul := Nat.casesOn n (@Mul.mul Int _) fun n => @Mul.mul (Finₓ n.succ) _
  mul_assoc := Nat.casesOn n (@mul_assoc Int _) fun n => @mul_assoc (Finₓ n.succ) _
  one := Nat.casesOn n (1 : Int) fun n => (1 : Finₓ n.succ)
  one_mul := Nat.casesOn n (@one_mulₓ Int _) fun n => @one_mulₓ (Finₓ n.succ) _
  mul_one := Nat.casesOn n (@mul_oneₓ Int _) fun n => @mul_oneₓ (Finₓ n.succ) _
  natCast := Nat.casesOn n (coe : ℕ → ℤ) fun n => (coe : ℕ → Finₓ n.succ)
  nat_cast_zero := Nat.casesOn n (@Nat.cast_zeroₓ Int _) fun n => @Nat.cast_zeroₓ (Finₓ n.succ) _
  nat_cast_succ := Nat.casesOn n (@Nat.cast_succₓ Int _) fun n => @Nat.cast_succₓ (Finₓ n.succ) _
  intCast := Nat.casesOn n (coe : ℤ → ℤ) fun n => (coe : ℤ → Finₓ n.succ)
  int_cast_of_nat := Nat.casesOn n (@Int.cast_of_nat Int _) fun n => @Int.cast_of_nat (Finₓ n.succ) _
  int_cast_neg_succ_of_nat :=
    Nat.casesOn n (@Int.cast_neg_succ_of_nat Int _) fun n => @Int.cast_neg_succ_of_nat (Finₓ n.succ) _
  left_distrib := Nat.casesOn n (@left_distrib Int _ _ _) fun n => @left_distrib (Finₓ n.succ) _ _ _
  right_distrib := Nat.casesOn n (@right_distrib Int _ _ _) fun n => @right_distrib (Finₓ n.succ) _ _ _
  mul_comm := Nat.casesOn n (@mul_comm Int _) fun n => @mul_comm (Finₓ n.succ) _

instance inhabited (n : ℕ) : Inhabited (Zmod n) :=
  ⟨0⟩

end Zmod

