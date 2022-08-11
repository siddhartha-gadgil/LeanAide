/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich
-/
import Mathbin.Data.Vector.Basic
import Mathbin.Data.Nat.Basic

/-!
# Basic operations on bitvectors

This is a work-in-progress, and contains additions to other theories.

This file was moved to mathlib from core Lean in the switch to Lean 3.20.0c.
It is not fully in compliance with mathlib style standards.
-/


/-- `bitvec n` is a `vector` of `bool` with length `n`. -/
@[reducible]
def Bitvec (n : ℕ) :=
  Vector Bool n

namespace Bitvec

open Nat

open Vector

-- mathport name: «expr ++ₜ »
local infixl:65 "++ₜ" => Vector.append

/-- Create a zero bitvector -/
@[reducible]
protected def zero (n : ℕ) : Bitvec n :=
  repeat false n

/-- Create a bitvector of length `n` whose `n-1`st entry is 1 and other entries are 0. -/
@[reducible]
protected def one : ∀ n : ℕ, Bitvec n
  | 0 => nil
  | succ n => repeat false n++ₜtt ::ᵥ nil

/-- Create a bitvector from another with a provably equal length. -/
protected def cong {a b : ℕ} (h : a = b) : Bitvec a → Bitvec b
  | ⟨x, p⟩ => ⟨x, h ▸ p⟩

/-- `bitvec` specific version of `vector.append` -/
def append {m n} : Bitvec m → Bitvec n → Bitvec (m + n) :=
  Vector.append

/-! ### Shift operations -/


section Shift

variable {n : ℕ}

/-- `shl x i` is the bitvector obtained by left-shifting `x` `i` times and padding with `ff`.
If `x.length < i` then this will return the all-`ff`s bitvector. -/
def shl (x : Bitvec n) (i : ℕ) : Bitvec n :=
  Bitvec.cong
      (by
        simp ) <|
    drop i x++ₜrepeat false (min n i)

/-- `fill_shr x i fill` is the bitvector obtained by right-shifting `x` `i` times and then
padding with `fill : bool`. If `x.length < i` then this will return the constant `fill`
bitvector. -/
def fillShr (x : Bitvec n) (i : ℕ) (fill : Bool) : Bitvec n :=
  Bitvec.cong
      (by
        by_cases' i ≤ n
        · have h₁ := Nat.sub_leₓ n i
          rw [min_eq_rightₓ h]
          rw [min_eq_leftₓ h₁, ← add_tsub_assoc_of_le h, Nat.add_comm, add_tsub_cancel_right]
          
        · have h₁ := le_of_not_geₓ h
          rw [min_eq_leftₓ h₁, tsub_eq_zero_iff_le.mpr h₁, zero_min, Nat.add_zero]
          ) <|
    repeat fill (min n i)++ₜtake (n - i) x

/-- unsigned shift right -/
def ushr (x : Bitvec n) (i : ℕ) : Bitvec n :=
  fillShr x i false

/-- signed shift right -/
def sshr : ∀ {m : ℕ}, Bitvec m → ℕ → Bitvec m
  | 0, _, _ => nil
  | succ m, x, i => head x ::ᵥ fillShr (tail x) i (head x)

end Shift

/-! ### Bitwise operations -/


section Bitwise

variable {n : ℕ}

/-- bitwise not -/
def not : Bitvec n → Bitvec n :=
  map bnot

/-- bitwise and -/
def and : Bitvec n → Bitvec n → Bitvec n :=
  map₂ band

/-- bitwise or -/
def or : Bitvec n → Bitvec n → Bitvec n :=
  map₂ bor

/-- bitwise xor -/
def xor : Bitvec n → Bitvec n → Bitvec n :=
  map₂ bxor

end Bitwise

/-! ### Arithmetic operators -/


section Arith

variable {n : ℕ}

/-- `xor3 x y c` is `((x XOR y) XOR c)`. -/
protected def xor3 (x y c : Bool) :=
  bxor (bxor x y) c

/-- `carry x y c` is `x && y || x && c || y && c`. -/
protected def carry (x y c : Bool) :=
  x && y || x && c || y && c

/-- `neg x` is the two's complement of `x`. -/
protected def neg (x : Bitvec n) : Bitvec n :=
  let f := fun y c => (y || c, bxor y c)
  Prod.snd (mapAccumr f x false)

/-- Add with carry (no overflow) -/
def adc (x y : Bitvec n) (c : Bool) : Bitvec (n + 1) :=
  let f := fun x y c => (Bitvec.carry x y c, Bitvec.xor3 x y c)
  let ⟨c, z⟩ := Vector.mapAccumr₂ f x y c
  c ::ᵥ z

/-- The sum of two bitvectors -/
protected def add (x y : Bitvec n) : Bitvec n :=
  tail (adc x y false)

/-- Subtract with borrow -/
def sbb (x y : Bitvec n) (b : Bool) : Bool × Bitvec n :=
  let f := fun x y c => (Bitvec.carry (bnot x) y c, Bitvec.xor3 x y c)
  Vector.mapAccumr₂ f x y b

/-- The difference of two bitvectors -/
protected def sub (x y : Bitvec n) : Bitvec n :=
  Prod.snd (sbb x y false)

instance : Zero (Bitvec n) :=
  ⟨Bitvec.zero n⟩

instance : One (Bitvec n) :=
  ⟨Bitvec.one n⟩

instance : Add (Bitvec n) :=
  ⟨Bitvec.add⟩

instance : Sub (Bitvec n) :=
  ⟨Bitvec.sub⟩

instance : Neg (Bitvec n) :=
  ⟨Bitvec.neg⟩

/-- The product of two bitvectors -/
protected def mul (x y : Bitvec n) : Bitvec n :=
  let f := fun r b => cond b (r + r + y) (r + r)
  (toList x).foldl f 0

instance : Mul (Bitvec n) :=
  ⟨Bitvec.mul⟩

end Arith

/-! ### Comparison operators -/


section Comparison

variable {n : ℕ}

/-- `uborrow x y` returns `tt` iff the "subtract with borrow" operation on `x`, `y` and `ff`
required a borrow. -/
def uborrow (x y : Bitvec n) : Bool :=
  Prod.fst (sbb x y false)

/-- unsigned less-than proposition -/
def Ult (x y : Bitvec n) : Prop :=
  uborrow x y

/-- unsigned greater-than proposition -/
def Ugt (x y : Bitvec n) : Prop :=
  Ult y x

/-- unsigned less-than-or-equal-to proposition -/
def Ule (x y : Bitvec n) : Prop :=
  ¬Ult y x

/-- unsigned greater-than-or-equal-to proposition -/
def Uge (x y : Bitvec n) : Prop :=
  Ule y x

/-- `sborrow x y` returns `tt` iff `x < y` as two's complement integers -/
def sborrow : ∀ {n : ℕ}, Bitvec n → Bitvec n → Bool
  | 0, _, _ => false
  | succ n, x, y =>
    match (head x, head y) with
    | (tt, ff) => true
    | (ff, tt) => false
    | _ => uborrow (tail x) (tail y)

/-- signed less-than proposition -/
def Slt (x y : Bitvec n) : Prop :=
  sborrow x y

/-- signed greater-than proposition -/
def Sgt (x y : Bitvec n) : Prop :=
  Slt y x

/-- signed less-than-or-equal-to proposition -/
def Sle (x y : Bitvec n) : Prop :=
  ¬Slt y x

/-- signed greater-than-or-equal-to proposition -/
def Sge (x y : Bitvec n) : Prop :=
  Sle y x

end Comparison

/-! ### Conversion to `nat` and `int` -/


section Conversion

variable {α : Type}

/-- Create a bitvector from a `nat` -/
protected def ofNat : ∀ n : ℕ, Nat → Bitvec n
  | 0, x => nil
  | succ n, x => of_nat n (x / 2)++ₜtoBool (x % 2 = 1) ::ᵥ nil

/-- Create a bitvector in the two's complement representation from an `int` -/
protected def ofInt : ∀ n : ℕ, Int → Bitvec (succ n)
  | n, Int.ofNat m => ff ::ᵥ Bitvec.ofNat n m
  | n, Int.negSucc m => tt ::ᵥ not (Bitvec.ofNat n m)

/-- `add_lsb r b` is `r + r + 1` if `b` is `tt` and `r + r` otherwise. -/
def addLsb (r : ℕ) (b : Bool) :=
  r + r + cond b 1 0

/-- Given a `list` of `bool`s, return the `nat` they represent as a list of binary digits. -/
def bitsToNat (v : List Bool) : Nat :=
  v.foldl addLsb 0

/-- Return the natural number encoded by the input bitvector -/
protected def toNat {n : Nat} (v : Bitvec n) : Nat :=
  bitsToNat (toList v)

theorem bits_to_nat_to_list {n : ℕ} (x : Bitvec n) : Bitvec.toNat x = bitsToNat (Vector.toList x) :=
  rfl

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.mul_comm Nat.mul_assoc

attribute [local simp] Nat.zero_add Nat.add_zero Nat.one_mul Nat.mul_one Nat.zero_mul Nat.mul_zero

-- mul_left_comm
theorem to_nat_append {m : ℕ} (xs : Bitvec m) (b : Bool) :
    Bitvec.toNat (xs++ₜb ::ᵥ nil) = Bitvec.toNat xs * 2 + Bitvec.toNat (b ::ᵥ nil) := by
  cases' xs with xs P
  simp [← bits_to_nat_to_list]
  clear P
  unfold bits_to_nat List.foldlₓ
  -- generalize the accumulator of foldl
  generalize h : 0 = x
  conv in add_lsb x b => rw [← h]
  clear h
  simp
  induction' xs with x xs generalizing x
  · simp
    unfold List.foldlₓ add_lsb
    simp [← Nat.mul_succ]
    
  · simp
    apply xs_ih
    

theorem bits_to_nat_to_bool (n : ℕ) : Bitvec.toNat (toBool (n % 2 = 1) ::ᵥ nil) = n % 2 := by
  simp [← bits_to_nat_to_list]
  unfold bits_to_nat add_lsb List.foldlₓ cond
  simp [← cond_to_bool_mod_two]

theorem of_nat_succ {k n : ℕ} : Bitvec.ofNat (succ k) n = Bitvec.ofNat k (n / 2)++ₜtoBool (n % 2 = 1) ::ᵥ nil :=
  rfl

theorem to_nat_of_nat {k n : ℕ} : Bitvec.toNat (Bitvec.ofNat k n) = n % 2 ^ k := by
  induction' k with k ih generalizing n
  · simp [← Nat.mod_oneₓ]
    rfl
    
  · rw [of_nat_succ, to_nat_append, ih, bits_to_nat_to_bool, mod_pow_succ, Nat.mul_comm]
    

/-- Return the integer encoded by the input bitvector -/
protected def toInt : ∀ {n : Nat}, Bitvec n → Int
  | 0, _ => 0
  | succ n, v => cond (head v) (Int.negSucc <| Bitvec.toNat <| Not <| tail v) (Int.ofNat <| Bitvec.toNat <| tail v)

end Conversion

/-! ### Miscellaneous instances -/


private def repr {n : Nat} : Bitvec n → Stringₓ
  | ⟨bs, p⟩ => "0b" ++ (bs.map fun b : Bool => if b then '1' else '0').asString

instance (n : Nat) : HasRepr (Bitvec n) :=
  ⟨reprₓ⟩

end Bitvec

instance {n} {x y : Bitvec n} : Decidable (Bitvec.Ult x y) :=
  Bool.decidableEq _ _

instance {n} {x y : Bitvec n} : Decidable (Bitvec.Ugt x y) :=
  Bool.decidableEq _ _

