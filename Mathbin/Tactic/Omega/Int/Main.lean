/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/
import Mathbin.Tactic.Omega.ProveUnsats
import Mathbin.Tactic.Omega.Int.Dnf

/-
Main procedure for linear integer arithmetic.
-/
open Tactic

namespace Omega

namespace Int

open Omega.Int

run_cmd
  mk_simp_attr `sugar

attribute [sugar]
  Ne not_leₓ not_ltₓ Int.lt_iff_add_one_leₓ or_falseₓ false_orₓ and_trueₓ true_andₓ Ge Gt mul_addₓ add_mulₓ one_mulₓ mul_oneₓ mul_comm sub_eq_add_neg imp_iff_not_or iff_iff_not_or_and_or_not

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
unsafe def desugar :=
  sorry

theorem univ_close_of_unsat_clausify (m : Nat) (p : Preform) : Clauses.Unsat (dnf (¬* p)) → UnivClose p (fun x => 0) m
  | h1 => by
    apply univ_close_of_valid
    apply valid_of_unsat_not
    apply unsat_of_clauses_unsat
    exact h1

/-- Given a (p : preform), return the expr of a (t : univ_close m p) -/
unsafe def prove_univ_close (m : Nat) (p : Preform) : tactic expr := do
  let x ← prove_unsats (dnf (¬* p))
  return (quote.1 (univ_close_of_unsat_clausify (%%ₓquote.1 m) (%%ₓquote.1 p) (%%ₓx)))

/-- Reification to imtermediate shadow syntax that retains exprs -/
unsafe def to_exprterm : expr → tactic exprterm
  | quote.1 (-%%ₓx) =>
    (--return (exprterm.exp (-1 : int) x)
      do
        let z ← eval_expr' Int x
        return (exprterm.cst (-z : Int))) <|>
      (return <| exprterm.exp (-1 : Int) x)
  | quote.1 ((%%ₓmx) * %%ₓzx) => do
    let z ← eval_expr' Int zx
    return (exprterm.exp z mx)
  | quote.1 ((%%ₓt1x) + %%ₓt2x) => do
    let t1 ← to_exprterm t1x
    let t2 ← to_exprterm t2x
    return (exprterm.add t1 t2)
  | x =>
    (do
        let z ← eval_expr' Int x
        return (exprterm.cst z)) <|>
      (return <| exprterm.exp 1 x)

/-- Reification to imtermediate shadow syntax that retains exprs -/
unsafe def to_exprform : expr → tactic exprform
  | quote.1 ((%%ₓtx1) = %%ₓtx2) => do
    let t1 ← to_exprterm tx1
    let t2 ← to_exprterm tx2
    return (exprform.eq t1 t2)
  | quote.1 ((%%ₓtx1) ≤ %%ₓtx2) => do
    let t1 ← to_exprterm tx1
    let t2 ← to_exprterm tx2
    return (exprform.le t1 t2)
  | quote.1 ¬%%ₓpx => do
    let p ← to_exprform px
    return (exprform.not p)
  | quote.1 ((%%ₓpx) ∨ %%ₓqx) => do
    let p ← to_exprform px
    let q ← to_exprform qx
    return (exprform.or p q)
  | quote.1 ((%%ₓpx) ∧ %%ₓqx) => do
    let p ← to_exprform px
    let q ← to_exprform qx
    return (exprform.and p q)
  | quote.1 (_ → %%ₓpx) => to_exprform px
  | x => (trace "Cannot reify expr : " >> trace x) >> failed

/-- List of all unreified exprs -/
unsafe def exprterm.exprs : exprterm → List expr
  | exprterm.cst _ => []
  | exprterm.exp _ x => [x]
  | exprterm.add t s => List.unionₓ t.exprs s.exprs

/-- List of all unreified exprs -/
unsafe def exprform.exprs : exprform → List expr
  | exprform.eq t s => List.unionₓ t.exprs s.exprs
  | exprform.le t s => List.unionₓ t.exprs s.exprs
  | exprform.not p => p.exprs
  | exprform.or p q => List.unionₓ p.exprs q.exprs
  | exprform.and p q => List.unionₓ p.exprs q.exprs

/-- Reification to an intermediate shadow syntax which eliminates exprs,
    but still includes non-canonical terms -/
unsafe def exprterm.to_preterm (xs : List expr) : exprterm → tactic Preterm
  | exprterm.cst k => return (&k)
  | exprterm.exp k x =>
    let m := xs.indexOf x
    if m < xs.length then return (k ** m) else failed
  | exprterm.add xa xb => do
    let a ← xa.to_preterm
    let b ← xb.to_preterm
    return (a+*b)

/-- Reification to an intermediate shadow syntax which eliminates exprs,
    but still includes non-canonical terms -/
unsafe def exprform.to_preform (xs : List expr) : exprform → tactic Preform
  | exprform.eq xa xb => do
    let a ← xa.to_preterm xs
    let b ← xb.to_preterm xs
    return (a =* b)
  | exprform.le xa xb => do
    let a ← xa.to_preterm xs
    let b ← xb.to_preterm xs
    return (a ≤* b)
  | exprform.not xp => do
    let p ← xp.to_preform
    return (¬* p)
  | exprform.or xp xq => do
    let p ← xp.to_preform
    let q ← xq.to_preform
    return (p ∨* q)
  | exprform.and xp xq => do
    let p ← xp.to_preform
    let q ← xq.to_preform
    return (p ∧* q)

/-- Reification to an intermediate shadow syntax which eliminates exprs,
    but still includes non-canonical terms. -/
unsafe def to_preform (x : expr) : tactic (preform × Nat) := do
  let xf ← to_exprform x
  let xs := xf.exprs
  let f ← xf.to_preform xs
  return (f, xs)

/-- Return expr of proof of current LIA goal -/
unsafe def prove : tactic expr := do
  let (p, m) ← target >>= to_preform
  trace_if_enabled `omega p
  prove_univ_close m p

/-- Succeed iff argument is the expr of ℤ -/
unsafe def eq_int (x : expr) : tactic Unit :=
  if x = quote.1 Int then skip else failed

/-- Check whether argument is expr of a well-formed formula of LIA-/
unsafe def wff : expr → tactic Unit
  | quote.1 ¬%%ₓpx => wff px
  | quote.1 ((%%ₓpx) ∨ %%ₓqx) => wff px >> wff qx
  | quote.1 ((%%ₓpx) ∧ %%ₓqx) => wff px >> wff qx
  | quote.1 ((%%ₓpx) ↔ %%ₓqx) => wff px >> wff qx
  | quote.1 (%%ₓexpr.pi _ _ px qx) =>
    Monadₓ.cond (if expr.has_var px then return true else is_prop px) (wff px >> wff qx) (eq_int px >> wff qx)
  | quote.1 (@LT.lt (%%ₓdx) (%%ₓh) _ _) => eq_int dx
  | quote.1 (@LE.le (%%ₓdx) (%%ₓh) _ _) => eq_int dx
  | quote.1 (@Eq (%%ₓdx) _ _) => eq_int dx
  | quote.1 (@Ge (%%ₓdx) (%%ₓh) _ _) => eq_int dx
  | quote.1 (@Gt (%%ₓdx) (%%ₓh) _ _) => eq_int dx
  | quote.1 (@Ne (%%ₓdx) _ _) => eq_int dx
  | quote.1 True => skip
  | quote.1 False => skip
  | _ => failed

/-- Succeed iff argument is expr of term whose type is wff -/
unsafe def wfx (x : expr) : tactic Unit :=
  infer_type x >>= wff

/-- Intro all universal quantifiers over ℤ -/
unsafe def intro_ints_core : tactic Unit := do
  let x ← target
  match x with
    | expr.pi _ _ (quote.1 Int) _ => intro_fresh >> intro_ints_core
    | _ => skip

unsafe def intro_ints : tactic Unit := do
  let expr.pi _ _ (quote.1 Int) _ ← target
  intro_ints_core

/-- If the goal has universal quantifiers over integers, introduce all of them.
Otherwise, revert all hypotheses that are formulas of linear integer arithmetic. -/
unsafe def preprocess : tactic Unit :=
  intro_ints <|> revert_cond_all wfx >> desugar

end Int

end Omega

open Omega.Int

/-- The core omega tactic for integers. -/
unsafe def omega_int (is_manual : Bool) : tactic Unit :=
  andthen (andthen desugar (if is_manual then skip else preprocess)) ((prove >>= apply) >> skip)

