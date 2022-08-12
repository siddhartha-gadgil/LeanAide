/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Nat.Pairing
import Mathbin.Data.Pnat.Basic

/-!
# Equivalences involving `ℕ`

This file defines some additional constructive equivalences using `encodable` and the pairing
function on `ℕ`.
-/


open Nat

namespace Equivₓ

variable {α : Type _}

/-- An equivalence between `ℕ × ℕ` and `ℕ`, using the `mkpair` and `unpair` functions in
`data.nat.pairing`.
-/
@[simp]
def natProdNatEquivNat : ℕ × ℕ ≃ ℕ :=
  ⟨fun p => Nat.mkpair p.1 p.2, Nat.unpair, fun p => by
    cases p
    apply Nat.unpair_mkpair, Nat.mkpair_unpair⟩

/-- An equivalence between `bool × ℕ` and `ℕ`, by mapping `(tt, x)` to `2 * x + 1` and `(ff, x)` to
`2 * x`.
-/
@[simp]
def boolProdNatEquivNat : Bool × ℕ ≃ ℕ :=
  ⟨fun ⟨b, n⟩ => bit b n, boddDiv2, fun ⟨b, n⟩ => by
    simp [← bool_prod_nat_equiv_nat._match_1, ← bodd_bit, ← div2_bit], fun n => by
    simp [← bool_prod_nat_equiv_nat._match_1, ← bit_decomp]⟩

/-- An equivalence between `ℕ ⊕ ℕ` and `ℕ`, by mapping `(sum.inl x)` to `2 * x` and `(sum.inr x)` to
`2 * x + 1`.
-/
@[simp]
def natSumNatEquivNat : Sum ℕ ℕ ≃ ℕ :=
  (boolProdEquivSum ℕ).symm.trans boolProdNatEquivNat

/-- An equivalence between `ℤ` and `ℕ`, through `ℤ ≃ ℕ ⊕ ℕ` and `ℕ ⊕ ℕ ≃ ℕ`.
-/
def intEquivNat : ℤ ≃ ℕ :=
  intEquivNatSumNat.trans natSumNatEquivNat

/-- An equivalence between `α × α` and `α`, given that there is an equivalence between `α` and `ℕ`.
-/
def prodEquivOfEquivNat (e : α ≃ ℕ) : α × α ≃ α :=
  calc
    α × α ≃ ℕ × ℕ := prodCongr e e
    _ ≃ ℕ := natProdNatEquivNat
    _ ≃ α := e.symm
    

/-- An equivalence between `ℕ+` and `ℕ`, by mapping `x` in `ℕ+` to `x - 1` in `ℕ`.
-/
def pnatEquivNat : ℕ+ ≃ ℕ :=
  ⟨fun n => pred n.1, succPnat, fun ⟨n, h⟩ => by
    cases n
    cases h
    simp [← succ_pnat, ← h], fun n => by
    simp [← succ_pnat]⟩

end Equivₓ

