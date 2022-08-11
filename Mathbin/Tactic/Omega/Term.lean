/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/
import Mathbin.Tactic.Omega.Coeffs

/-
Normalized linear integer arithmetic terms.
-/
namespace Omega

/-- Shadow syntax of normalized terms. The first element
    represents the constant term and the list represents
    the coefficients. -/
def Term : Type :=
  Int × List Int deriving Inhabited

unsafe instance : has_reflect Term :=
  prod.has_reflect _ _

namespace Term

/-- Evaluate a term using the valuation v. -/
@[simp]
def val (v : Nat → Int) : Term → Int
  | (b, as) => b + Coeffs.val v as

@[simp]
def neg : Term → Term
  | (b, as) => (-b, List.Func.neg as)

@[simp]
def add : Term → Term → Term
  | (c1, cfs1), (c2, cfs2) => (c1 + c2, List.Func.add cfs1 cfs2)

@[simp]
def sub : Term → Term → Term
  | (c1, cfs1), (c2, cfs2) => (c1 - c2, List.Func.sub cfs1 cfs2)

@[simp]
def mul (i : Int) : Term → Term
  | (b, as) => (i * b, as.map ((· * ·) i))

@[simp]
def div (i : Int) : Term → Term
  | (b, as) => (b / i, as.map fun x => x / i)

theorem val_neg {v : Nat → Int} {t : Term} : (neg t).val v = -t.val v := by
  cases' t with b as
  simp only [← val, ← neg_add, ← neg, ← val, ← coeffs.val_neg]

@[simp]
theorem val_sub {v : Nat → Int} {t1 t2 : Term} : (sub t1 t2).val v = t1.val v - t2.val v := by
  cases t1
  cases t2
  simp only [← add_assocₓ, ← coeffs.val_sub, ← neg_add_rev, ← val, ← sub, ← add_commₓ, ← add_left_commₓ, ←
    sub_eq_add_neg]

@[simp]
theorem val_add {v : Nat → Int} {t1 t2 : Term} : (add t1 t2).val v = t1.val v + t2.val v := by
  cases t1
  cases t2
  simp only [← coeffs.val_add, ← add, ← val, ← add_commₓ, ← add_left_commₓ]

@[simp]
theorem val_mul {v : Nat → Int} {i : Int} {t : Term} : val v (mul i t) = i * val v t := by
  cases t
  simp only [← mul, ← mul_addₓ, ← add_mulₓ, ← List.length_mapₓ, ← coeffs.val, ← coeffs.val_between_map_mul, ← val, ←
    List.map]

theorem val_div {v : Nat → Int} {i b : Int} {as : List Int} :
    i ∣ b → (∀, ∀ x ∈ as, ∀, i ∣ x) → (div i (b, as)).val v = val v (b, as) / i := by
  intro h1 h2
  simp only [← val, ← div, ← List.map]
  rw [Int.add_div_of_dvd_left h1]
  apply fun_mono_2 rfl
  rw [← coeffs.val_map_div h2]

/-- Fresh de Brujin index not used by any variable ocurring in the term -/
def freshIndex (t : Term) : Nat :=
  t.snd.length

def toString (t : Term) : Stringₓ :=
  t.2.enum.foldr (fun ⟨i, n⟩ r => toString n ++ " * x" ++ toString i ++ " + " ++ r) (toString t.1)

instance : HasToString Term :=
  ⟨toString⟩

end Term

/-- Fresh de Brujin index not used by any variable ocurring in the list of terms -/
def Terms.freshIndex : List Term → Nat
  | [] => 0
  | t :: ts => max t.freshIndex (terms.fresh_index ts)

end Omega

