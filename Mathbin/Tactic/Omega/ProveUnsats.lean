/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/
import Mathbin.Tactic.Omega.FindEes
import Mathbin.Tactic.Omega.FindScalars
import Mathbin.Tactic.Omega.LinComb

/-
A tactic which constructs exprs to discharge
goals of the form `clauses.unsat cs`.
-/
namespace Omega

open Tactic

/-- Return expr of proof that given int is negative -/
unsafe def prove_neg : Int → tactic expr
  | Int.ofNat _ => failed
  | -[1+ m] => return (quote.1 (Int.neg_succ_lt_zeroₓ (%%ₓquote.1 m)))

theorem forall_mem_repeat_zero_eq_zero (m : Nat) : ∀, ∀ x ∈ List.repeat (0 : Int) m, ∀, x = (0 : Int) := fun x =>
  List.eq_of_mem_repeat

/-- Return expr of proof that elements of (repeat 0 is.length) are all 0 -/
unsafe def prove_forall_mem_eq_zero (is : List Int) : tactic expr :=
  return (quote.1 (forall_mem_repeat_zero_eq_zero is.length))

/-- Return expr of proof that the combination of linear constraints
    represented by ks and ts is unsatisfiable -/
unsafe def prove_unsat_lin_comb (ks : List Nat) (ts : List Term) : tactic expr :=
  let ⟨b, as⟩ := linComb ks ts
  do
  let x1 ← prove_neg b
  let x2 ← prove_forall_mem_eq_zero as
  to_expr (pquote.1 (unsat_lin_comb_of (%%ₓquote.1 ks) (%%ₓquote.1 ts) (%%ₓx1) (%%ₓx2)))

/-- Given a (([],les) : clause), return the expr of a term (t : clause.unsat ([],les)). -/
unsafe def prove_unsat_ef : Clause → tactic expr
  | (_ :: _, _) => failed
  | ([], les) => do
    let ks ← find_scalars les
    let x ← prove_unsat_lin_comb ks les
    return (quote.1 (unsat_of_unsat_lin_comb (%%ₓquote.1 ks) (%%ₓquote.1 les) (%%ₓx)))

/-- Given a (c : clause), return the expr of a term (t : clause.unsat c)  -/
unsafe def prove_unsat (c : Clause) : tactic expr := do
  let ee ← find_ees c
  let x ← prove_unsat_ef (eqElim ee c)
  return (quote.1 (unsat_of_unsat_eq_elim (%%ₓquote.1 ee) (%%ₓquote.1 c) (%%ₓx)))

/-- Given a (cs : list clause), return the expr of a term (t : clauses.unsat cs)  -/
unsafe def prove_unsats : List Clause → tactic expr
  | [] => return (quote.1 Clauses.unsat_nil)
  | p :: ps => do
    let x ← prove_unsat p
    let xs ← prove_unsats ps
    to_expr (pquote.1 (Clauses.unsat_cons (%%ₓquote.1 p) (%%ₓquote.1 ps) (%%ₓx) (%%ₓxs)))

end Omega

