/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/
import Mathbin.Tactic.Omega.Term

/-
Linear integer arithmetic terms in pre-normalized form.
-/
namespace Omega

namespace Int

/-- The shadow syntax for arithmetic terms. All constants are reified to `cst`
(e.g., `-5` is reified to `cst -5`) and all other atomic terms are reified to
`exp` (e.g., `-5 * (gcd 14 -7)` is reified to `exp -5 \`(gcd 14 -7)`).
`exp` accepts a coefficient of type `int` as its first argument because
multiplication by constant is allowed by the omega test. -/
unsafe inductive exprterm : Type
  | cst : Int → exprterm
  | exp : Int → expr → exprterm
  | add : exprterm → exprterm → exprterm

/-- Similar to `exprterm`, except that all exprs are now replaced with
de Brujin indices of type `nat`. This is akin to generalizing over
the terms represented by the said exprs. -/
inductive Preterm : Type
  | cst : Int → preterm
  | var : Int → Nat → preterm
  | add : preterm → preterm → preterm
  deriving has_reflect, Inhabited

-- mathport name: «expr& »
localized [Omega.Int] notation "&" k => Omega.Int.Preterm.cst k

-- mathport name: «expr ** »
localized [Omega.Int] infixl:300 " ** " => Omega.Int.Preterm.var

-- mathport name: «expr +* »
localized [Omega.Int] notation t "+*" s => Omega.Int.Preterm.add t s

namespace Preterm

/-- Preterm evaluation -/
@[simp]
def val (v : Nat → Int) : Preterm → Int
  | &i => i
  | i ** n => if i = 1 then v n else if i = -1 then -v n else v n * i
  | t1+*t2 => t1.val + t2.val

/-- Fresh de Brujin index not used by any variable in argument -/
def freshIndex : Preterm → Nat
  | &_ => 0
  | i ** n => n + 1
  | t1+*t2 => max t1.freshIndex t2.freshIndex

@[simp]
def addOne (t : Preterm) : Preterm :=
  t+*&1

def repr : Preterm → Stringₓ
  | &i => i.repr
  | i ** n => i.repr ++ "*x" ++ n.repr
  | t1+*t2 => "(" ++ t1.repr ++ " + " ++ t2.repr ++ ")"

end Preterm

open List.Func

/-- Return a term (which is in canonical form by definition)
    that is equivalent to the input preterm -/
-- get notation for list.func.set
@[simp]
def canonize : Preterm → Term
  | &i => ⟨i, []⟩
  | i ** n => ⟨0, [] {n ↦ i}⟩
  | t1+*t2 => Term.add (canonize t1) (canonize t2)

@[simp]
theorem val_canonize {v : Nat → Int} : ∀ {t : Preterm}, (canonize t).val v = t.val v
  | &i => by
    simp only [← preterm.val, ← add_zeroₓ, ← term.val, ← canonize, ← coeffs.val_nil]
  | i ** n => by
    simp only [← coeffs.val_set, ← canonize, ← preterm.val, ← zero_addₓ, ← term.val]
    split_ifs with h1 h2
    · simp only [← one_mulₓ, ← h1]
      
    · simp only [← neg_mul, ← one_mulₓ, ← h2]
      
    · rw [mul_comm]
      
  | t+*s => by
    simp only [← canonize, ← val_canonize, ← term.val_add, ← preterm.val]

end Int

end Omega

