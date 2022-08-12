/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathbin.Tactic.Linarith.Datatypes

/-!
# Parsing input expressions into linear form

`linarith` computes the linear form of its input expressions,
assuming (without justification) that the type of these expressions
is a commutative semiring.
It identifies atoms up to ring-equivalence: that is, `(y*3)*x` will be identified `3*(x*y)`,
where the monomial `x*y` is the linear atom.

* Variables are represented by natural numbers.
* Monomials are represented by `monom := rb_map ℕ ℕ`.
  The monomial `1` is represented by the empty map.
* Linear combinations of monomials are represented by `sum := rb_map monom ℤ`.

All input expressions are converted to `sum`s, preserving the map from expressions to variables.
We then discard the monomial information, mapping each distinct monomial to a natural number.
The resulting `rb_map ℕ ℤ` represents the ring-normalized linear form of the expression.
This is ultimately converted into a `linexp` in the obvious way.

`linear_forms_and_vars` is the main entry point into this file. Everything else is contained.
-/


open Native Linarith.Ineq Tactic

namespace Linarith

/-! ### Parsing datatypes -/


/-- Variables (represented by natural numbers) map to their power. -/
@[reducible]
unsafe def monom : Type :=
  rb_map ℕ ℕ

/-- `1` is represented by the empty monomial, the product of no variables. -/
unsafe def monom.one : monom :=
  rb_map.mk _ _

/-- Compare monomials by first comparing their keys and then their powers. -/
@[reducible]
unsafe def monom.lt : monom → monom → Prop := fun a b => a.keys < b.keys || a.keys = b.keys && a.values < b.values

unsafe instance : LT monom :=
  ⟨monom.lt⟩

/-- Linear combinations of monomials are represented by mapping monomials to coefficients. -/
@[reducible]
unsafe def sum : Type :=
  rb_map monom ℤ

/-- `1` is represented as the singleton sum of the monomial `monom.one` with coefficient 1. -/
unsafe def sum.one : sum :=
  rb_map.of_list [(monom.one, 1)]

/-- `sum.scale_by_monom s m` multiplies every monomial in `s` by `m`. -/
unsafe def sum.scale_by_monom (s : sum) (m : monom) : sum :=
  (s.fold mk_rb_map) fun m' coeff sm => sm.insert (m.add m') coeff

/-- `sum.mul s1 s2` distributes the multiplication of two sums.` -/
unsafe def sum.mul (s1 s2 : sum) : sum :=
  (s1.fold mk_rb_map) fun mn coeff sm => sm.add <| (s2.scale_by_monom mn).scale coeff

/-- The `n`th power of `s : sum` is the `n`-fold product of `s`, with `s.pow 0 = sum.one`. -/
unsafe def sum.pow (s : sum) : ℕ → sum
  | 0 => sum.one
  | k + 1 => s.mul (sum.pow k)

/-- `sum_of_monom m` lifts `m` to a sum with coefficient `1`. -/
unsafe def sum_of_monom (m : monom) : sum :=
  mk_rb_map.insert m 1

/-- The unit monomial `one` is represented by the empty rb map. -/
unsafe def one : monom :=
  mk_rb_map

/-- A scalar `z` is represented by a `sum` with coefficient `z` and monomial `one` -/
unsafe def scalar (z : ℤ) : sum :=
  mk_rb_map.insert one z

/-- A single variable `n` is represented by a sum with coefficient `1` and monomial `n`. -/
unsafe def var (n : ℕ) : sum :=
  mk_rb_map.insert (mk_rb_map.insert n 1) 1

/-! ### Parsing algorithms -/


-- mathport name: «exprexmap»
local notation "exmap" => List (expr × ℕ)

/-- `linear_form_of_atom red map e` is the atomic case for `linear_form_of_expr`.
If `e` appears with index `k` in `map`, it returns the singleton sum `var k`.
Otherwise it updates `map`, adding `e` with index `n`, and returns the singleton sum `var n`.
-/
unsafe def linear_form_of_atom (red : Transparency) (m : exmap) (e : expr) : tactic (exmap × Sum) :=
  (do
      let (_, k) ← m.find_defeq red e
      return (m, var k)) <|>
    let n := m.length + 1
    return ((e, n) :: m, var n)

/-- `linear_form_of_expr red map e` computes the linear form of `e`.

`map` is a lookup map from atomic expressions to variable numbers.
If a new atomic expression is encountered, it is added to the map with a new number.
It matches atomic expressions up to reducibility given by `red`.

Because it matches up to definitional equality, this function must be in the `tactic` monad,
and forces some functions that call it into `tactic` as well.
-/
unsafe def linear_form_of_expr (red : Transparency) : exmap → expr → tactic (exmap × Sum)
  | m, e@(quote.1 ((%%ₓe1) * %%ₓe2)) => do
    let (m', comp1) ← linear_form_of_expr m e1
    let (m', comp2) ← linear_form_of_expr m' e2
    return (m', comp1 comp2)
  | m, quote.1 ((%%ₓe1) + %%ₓe2) => do
    let (m', comp1) ← linear_form_of_expr m e1
    let (m', comp2) ← linear_form_of_expr m' e2
    return (m', comp1 comp2)
  | m, quote.1 ((%%ₓe1) - %%ₓe2) => do
    let (m', comp1) ← linear_form_of_expr m e1
    let (m', comp2) ← linear_form_of_expr m' e2
    return (m', comp1 (comp2 (-1)))
  | m, quote.1 (-%%ₓe) => do
    let (m', comp) ← linear_form_of_expr m e
    return (m', comp (-1))
  | m, p@(quote.1 (@Pow.pow _ ℕ _ (%%ₓe) (%%ₓn))) =>
    match n.toNat with
    | some k => do
      let (m', comp) ← linear_form_of_expr m e
      return (m', comp k)
    | none => linear_form_of_atom red m p
  | m, e =>
    match e.to_int with
    | some 0 => return ⟨m, mk_rb_map⟩
    | some z => return ⟨m, scalar z⟩
    | none => linear_form_of_atom red m e

/-- `sum_to_lf s map` eliminates the monomial level of the `sum` `s`.

`map` is a lookup map from monomials to variable numbers.
The output `rb_map ℕ ℤ` has the same structure as `sum`,
but each monomial key is replaced with its index according to `map`.
If any new monomials are encountered, they are assigned variable numbers and `map` is updated.
 -/
unsafe def sum_to_lf (s : sum) (m : rb_map monom ℕ) : rb_map monom ℕ × rb_map ℕ ℤ :=
  (s.fold (m, mk_rb_map)) fun mn coeff ⟨map, out⟩ =>
    match map.find mn with
    | some n => ⟨map, out.insert n coeff⟩
    | none =>
      let n := map.size
      ⟨map.insert mn n, out.insert n coeff⟩

/-- `to_comp red e e_map monom_map` converts an expression of the form `t < 0`, `t ≤ 0`, or `t = 0`
into a `comp` object.

`e_map` maps atomic expressions to indices; `monom_map` maps monomials to indices.
Both of these are updated during processing and returned.
-/
unsafe def to_comp (red : Transparency) (e : expr) (e_map : exmap) (monom_map : rb_map monom ℕ) :
    tactic (comp × exmap × rb_map monom ℕ) := do
  let (iq, e) ← parse_into_comp_and_expr e
  let (m', comp') ← linear_form_of_expr red e_map e
  let ⟨nm, mm'⟩ := sum_to_lf comp' monom_map
  return ⟨⟨iq, mm'⟩, m', nm⟩

/-- `to_comp_fold red e_map exprs monom_map` folds `to_comp` over `exprs`,
updating `e_map` and `monom_map` as it goes.
 -/
unsafe def to_comp_fold (red : Transparency) :
    exmap → List expr → rb_map monom ℕ → tactic (List Comp × exmap × rb_map monom ℕ)
  | m, [], mm => return ([], m, mm)
  | m, h :: t, mm => do
    let (c, m', mm') ← to_comp red h m mm
    let (l, mp, mm') ← to_comp_fold m' t mm'
    return (c :: l, mp, mm')

/-- `linear_forms_and_vars red pfs` is the main interface for computing the linear forms of a list
of expressions. Given a list `pfs` of proofs of comparisons, it produces a list `c` of `comps` of
the same length, such that `c[i]` represents the linear form of the type of `pfs[i]`.

It also returns the largest variable index that appears in comparisons in `c`.
-/
unsafe def linear_forms_and_max_var (red : Transparency) (pfs : List expr) : tactic (List Comp × ℕ) := do
  let pftps ← pfs.mmap infer_type
  let (l, _, map) ← to_comp_fold red [] pftps mk_rb_map
  return (l, map - 1)

end Linarith

