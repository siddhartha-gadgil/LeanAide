/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/
import Mathbin.Tactic.Omega.ProveUnsats
import Mathbin.Tactic.Omega.Nat.Dnf
import Mathbin.Tactic.Omega.Nat.NegElim
import Mathbin.Tactic.Omega.Nat.SubElim

/-
Main procedure for linear natural number arithmetic.
-/
open Tactic

namespace Omega

namespace Nat

open Omega.Nat

run_cmd
  mk_simp_attr `sugar_nat

attribute [sugar_nat]
  Ne not_leₓ not_ltₓ Nat.lt_iff_add_one_le Nat.succ_eq_add_one or_falseₓ false_orₓ and_trueₓ true_andₓ Ge Gt mul_addₓ add_mulₓ mul_comm one_mulₓ mul_oneₓ imp_iff_not_or iff_iff_not_or_and_or_not

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
unsafe def desugar :=
  sorry

theorem univ_close_of_unsat_neg_elim_not (m) (p : Preform) : (negElim (¬* p)).Unsat → UnivClose p (fun _ => 0) m := by
  intro h1
  apply univ_close_of_valid
  apply valid_of_unsat_not
  intro h2
  apply h1
  apply preform.sat_of_implies_of_sat implies_neg_elim h2

/-- Return expr of proof that argument is free of subtractions -/
unsafe def preterm.prove_sub_free : Preterm → tactic expr
  | &m => return (quote.1 trivialₓ)
  | m ** n => return (quote.1 trivialₓ)
  | t +* s => do
    let x ← preterm.prove_sub_free t
    let y ← preterm.prove_sub_free s
    return (quote.1 (@And.intro (Preterm.SubFree (%%ₓquote.1 t)) (Preterm.SubFree (%%ₓquote.1 s)) (%%ₓx) (%%ₓy)))
  | _ -* _ => failed

/-- Return expr of proof that argument is free of negations -/
unsafe def prove_neg_free : Preform → tactic expr
  | t =* s => return (quote.1 trivialₓ)
  | t ≤* s => return (quote.1 trivialₓ)
  | p ∨* q => do
    let x ← prove_neg_free p
    let y ← prove_neg_free q
    return (quote.1 (@And.intro (Preform.NegFree (%%ₓquote.1 p)) (Preform.NegFree (%%ₓquote.1 q)) (%%ₓx) (%%ₓy)))
  | p ∧* q => do
    let x ← prove_neg_free p
    let y ← prove_neg_free q
    return (quote.1 (@And.intro (Preform.NegFree (%%ₓquote.1 p)) (Preform.NegFree (%%ₓquote.1 q)) (%%ₓx) (%%ₓy)))
  | _ => failed

/-- Return expr of proof that argument is free of subtractions -/
unsafe def prove_sub_free : Preform → tactic expr
  | t =* s => do
    let x ← preterm.prove_sub_free t
    let y ← preterm.prove_sub_free s
    return (quote.1 (@And.intro (Preterm.SubFree (%%ₓquote.1 t)) (Preterm.SubFree (%%ₓquote.1 s)) (%%ₓx) (%%ₓy)))
  | t ≤* s => do
    let x ← preterm.prove_sub_free t
    let y ← preterm.prove_sub_free s
    return (quote.1 (@And.intro (Preterm.SubFree (%%ₓquote.1 t)) (Preterm.SubFree (%%ₓquote.1 s)) (%%ₓx) (%%ₓy)))
  | ¬* p => prove_sub_free p
  | p ∨* q => do
    let x ← prove_sub_free p
    let y ← prove_sub_free q
    return (quote.1 (@And.intro (Preform.SubFree (%%ₓquote.1 p)) (Preform.SubFree (%%ₓquote.1 q)) (%%ₓx) (%%ₓy)))
  | p ∧* q => do
    let x ← prove_sub_free p
    let y ← prove_sub_free q
    return (quote.1 (@And.intro (Preform.SubFree (%%ₓquote.1 p)) (Preform.SubFree (%%ₓquote.1 q)) (%%ₓx) (%%ₓy)))

/-- Given a p : preform, return the expr of a term t : p.unsat, where p is subtraction- and
negation-free. -/
unsafe def prove_unsat_sub_free (p : Preform) : tactic expr := do
  let x ← prove_neg_free p
  let y ← prove_sub_free p
  let z ← prove_unsats (dnf p)
  return (quote.1 (unsat_of_unsat_dnf (%%ₓquote.1 p) (%%ₓx) (%%ₓy) (%%ₓz)))

/-- Given a p : preform, return the expr of a term t : p.unsat, where p is negation-free. -/
unsafe def prove_unsat_neg_free : Preform → tactic expr
  | p =>
    match p.subTerms with
    | none => prove_unsat_sub_free p
    | some (t, s) => do
      let x ← prove_unsat_neg_free (subElim t s p)
      return (quote.1 (unsat_of_unsat_sub_elim (%%ₓquote.1 t) (%%ₓquote.1 s) (%%ₓquote.1 p) (%%ₓx)))

/-- Given a (m : nat) and (p : preform), return the expr of (t : univ_close m p). -/
unsafe def prove_univ_close (m : Nat) (p : Preform) : tactic expr := do
  let x ← prove_unsat_neg_free (negElim (¬* p))
  to_expr (pquote.1 (univ_close_of_unsat_neg_elim_not (%%ₓquote.1 m) (%%ₓquote.1 p) (%%ₓx)))

/-- Reification to imtermediate shadow syntax that retains exprs -/
unsafe def to_exprterm : expr → tactic exprterm
  | quote.1 ((%%ₓx) * %%ₓy) => do
    let m ← eval_expr' Nat y
    return (exprterm.exp m x)
  | quote.1 ((%%ₓt1x) + %%ₓt2x) => do
    let t1 ← to_exprterm t1x
    let t2 ← to_exprterm t2x
    return (exprterm.add t1 t2)
  | quote.1 ((%%ₓt1x) - %%ₓt2x) => do
    let t1 ← to_exprterm t1x
    let t2 ← to_exprterm t2x
    return (exprterm.sub t1 t2)
  | x =>
    (do
        let m ← eval_expr' Nat x
        return (exprterm.cst m)) <|>
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
  | exprterm.sub t s => List.unionₓ t.exprs s.exprs

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
    return (a +* b)
  | exprterm.sub xa xb => do
    let a ← xa.to_preterm
    let b ← xb.to_preterm
    return (a -* b)

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

/-- Return expr of proof of current LNA goal -/
unsafe def prove : tactic expr := do
  let (p, m) ← target >>= to_preform
  trace_if_enabled `omega p
  prove_univ_close m p

/-- Succeed iff argument is expr of ℕ -/
unsafe def eq_nat (x : expr) : tactic Unit :=
  if x = quote.1 Nat then skip else failed

/-- Check whether argument is expr of a well-formed formula of LNA-/
unsafe def wff : expr → tactic Unit
  | quote.1 ¬%%ₓpx => wff px
  | quote.1 ((%%ₓpx) ∨ %%ₓqx) => wff px >> wff qx
  | quote.1 ((%%ₓpx) ∧ %%ₓqx) => wff px >> wff qx
  | quote.1 ((%%ₓpx) ↔ %%ₓqx) => wff px >> wff qx
  | quote.1 (%%ₓexpr.pi _ _ px qx) =>
    Monadₓ.cond (if expr.has_var px then return true else is_prop px) (wff px >> wff qx) (eq_nat px >> wff qx)
  | quote.1 (@LT.lt (%%ₓdx) (%%ₓh) _ _) => eq_nat dx
  | quote.1 (@LE.le (%%ₓdx) (%%ₓh) _ _) => eq_nat dx
  | quote.1 (@Eq (%%ₓdx) _ _) => eq_nat dx
  | quote.1 (@Ge (%%ₓdx) (%%ₓh) _ _) => eq_nat dx
  | quote.1 (@Gt (%%ₓdx) (%%ₓh) _ _) => eq_nat dx
  | quote.1 (@Ne (%%ₓdx) _ _) => eq_nat dx
  | quote.1 True => skip
  | quote.1 False => skip
  | _ => failed

/-- Succeed iff argument is expr of term whose type is wff -/
unsafe def wfx (x : expr) : tactic Unit :=
  infer_type x >>= wff

/-- Intro all universal quantifiers over nat -/
unsafe def intro_nats_core : tactic Unit := do
  let x ← target
  match x with
    | expr.pi _ _ (quote.1 Nat) _ => intro_fresh >> intro_nats_core
    | _ => skip

unsafe def intro_nats : tactic Unit := do
  let expr.pi _ _ (quote.1 Nat) _ ← target
  intro_nats_core

/-- If the goal has universal quantifiers over natural, introduce all of them.
Otherwise, revert all hypotheses that are formulas of linear natural number arithmetic. -/
unsafe def preprocess : tactic Unit :=
  intro_nats <|> revert_cond_all wfx >> desugar

end Nat

end Omega

open Omega.Nat

/-- The core omega tactic for natural numbers. -/
unsafe def omega_nat (is_manual : Bool) : tactic Unit :=
  andthen (andthen desugar (if is_manual then skip else preprocess)) ((prove >>= apply) >> skip)

