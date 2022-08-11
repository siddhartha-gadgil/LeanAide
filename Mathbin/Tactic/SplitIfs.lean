/-
Copyright (c) 2018 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner

Tactic to split if-then-else-expressions.
-/
import Mathbin.Tactic.Hint

open Expr Tactic

namespace Tactic

setup_tactic_parser

unsafe def find_if_cond : expr → Option expr
  | e =>
    (e.fold none) fun e _ acc =>
      Acc <|> do
        let c ←
          match e with
            | quote.1 (@ite _ (%%ₓc) (%%ₓ_) _ _) => some c
            | quote.1 (@dite _ (%%ₓc) (%%ₓ_) _ _) => some c
            | _ => none
        guardₓ ¬c
        find_if_cond c <|> return c

unsafe def find_if_cond_at (at_ : Loc) : tactic (Option expr) := do
  let lctx ← at_.get_locals
  let lctx ← lctx.mmap infer_type
  let tgt ← target
  let es := if at_.include_goal then tgt :: lctx else lctx
  return <| find_if_cond <| es app default

run_cmd
  mk_simp_attr `split_if_reduction

run_cmd
  add_doc_string `simp_attr.split_if_reduction "Simp set for if-then-else statements"

attribute [split_if_reduction] if_pos if_neg dif_pos dif_neg if_congr

unsafe def reduce_ifs_at (at_ : Loc) : tactic Unit := do
  let sls ← get_user_simp_lemmas `split_if_reduction
  let cfg : SimpConfig := { failIfUnchanged := false }
  let discharger := assumption <|> applyc `not_not_intro >> assumption
  let hs ← at_.get_locals
  hs fun h => simp_hyp sls [] h cfg discharger >> skip
  when at_ (simp_target sls [] cfg discharger >> skip)

unsafe def split_if1 (c : expr) (n : Name) (at_ : Loc) : tactic Unit :=
  andthen (by_cases c n) (reduce_ifs_at at_)

private unsafe def get_next_name (names : ref (List Name)) : tactic Name := do
  let ns ← read_ref names
  match ns with
    | [] => get_unused_name `h
    | n :: ns => do
      write_ref names ns
      return n

private unsafe def value_known (c : expr) : tactic Bool := do
  let lctx ← local_context
  let lctx ← lctx.mmap infer_type
  return <| c ∈ lctx ∨ (quote.1 ¬%%ₓc) ∈ lctx

private unsafe def split_ifs_core (at_ : Loc) (names : ref (List Name)) : List expr → tactic Unit
  | done => do
    let some cond ← find_if_cond_at at_ | fail "no if-then-else expressions to split"
    let cond :=
      match cond with
      | quote.1 ¬%%ₓp => p
      | p => p
    if cond ∈ done then skip
      else do
        let no_split ← value_known cond
        if no_split then andthen (reduce_ifs_at at_) (try (split_ifs_core (cond :: done)))
          else do
            let n ← get_next_name names
            andthen (split_if1 cond n at_) (try (split_ifs_core (cond :: done)))

unsafe def split_ifs (names : List Name) (at_ : Loc := Loc.ns [none]) :=
  (using_new_ref names) fun names => split_ifs_core at_ names []

namespace Interactive

open Interactive Interactive.Types Expr Lean.Parser

/-- Splits all if-then-else-expressions into multiple goals.

Given a goal of the form `g (if p then x else y)`, `split_ifs` will produce
two goals: `p ⊢ g x` and `¬p ⊢ g y`.

If there are multiple ite-expressions, then `split_ifs` will split them all,
starting with a top-most one whose condition does not contain another
ite-expression.

`split_ifs at *` splits all ite-expressions in all hypotheses as well as the goal.

`split_ifs with h₁ h₂ h₃` overrides the default names for the hypotheses.
-/
unsafe def split_ifs (at_ : parse location) (names : parse with_ident_list) : tactic Unit :=
  tactic.split_ifs names at_

add_hint_tactic split_ifs

add_tactic_doc
  { Name := "split_ifs", category := DocCategory.tactic, declNames := [`` split_ifs], tags := ["case bashing"] }

end Interactive

end Tactic

