/-
Copyright (c) 2020 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Mathbin.Tactic.Lint.Basic

/-!
# Linter for simplification lemmas

This files defines several linters that prevent common mistakes when declaring simp lemmas:

 * `simp_nf` checks that the left-hand side of a simp lemma is not simplified by a different lemma.
 * `simp_var_head` checks that the head symbol of the left-hand side is not a variable.
 * `simp_comm` checks that commutativity lemmas are not marked as simplification lemmas.
-/


open Tactic Expr

/-- `simp_lhs_rhs ty` returns the left-hand and right-hand side of a simp lemma with type `ty`. -/
private unsafe def simp_lhs_rhs : expr → tactic (expr × expr)
  | ty => do
    let ty ← head_beta ty
    -- We only detect a fixed set of simp relations here.
      -- This is somewhat justified since for a custom simp relation R,
      -- the simp lemma `R a b` is implicitly converted to `R a b ↔ true` as well.
      match ty with
      | quote.1 ¬%%ₓlhs => pure (lhs, quote.1 False)
      | quote.1 ((%%ₓlhs) = %%ₓrhs) => pure (lhs, rhs)
      | quote.1 ((%%ₓlhs) ↔ %%ₓrhs) => pure (lhs, rhs)
      | expr.pi n bi a b => do
        let l ← mk_local' n bi a
        simp_lhs_rhs (b l)
      | ty => pure (ty, quote.1 True)

/-- `simp_lhs ty` returns the left-hand side of a simp lemma with type `ty`. -/
private unsafe def simp_lhs (ty : expr) : tactic expr :=
  Prod.fst <$> simp_lhs_rhs ty

/-- `simp_is_conditional_core ty` returns `none` if `ty` is a conditional simp
lemma, and `some lhs` otherwise.
-/
private unsafe def simp_is_conditional_core : expr → tactic (Option expr)
  | ty => do
    let ty ← head_beta ty
    match ty with
      | quote.1 ¬%%ₓlhs => pure lhs
      | quote.1 ((%%ₓlhs) = _) => pure lhs
      | quote.1 ((%%ₓlhs) ↔ _) => pure lhs
      | expr.pi n bi a b => do
        let l ← mk_local' n bi a
        let some lhs ← simp_is_conditional_core (b l) | pure none
        if bi ≠ BinderInfo.inst_implicit ∧ ¬(lhs l).has_var then pure none else pure lhs
      | ty => pure ty

/-- `simp_is_conditional ty` returns true iff the simp lemma with type `ty` is conditional.
-/
private unsafe def simp_is_conditional (ty : expr) : tactic Bool :=
  Option.isNone <$> simp_is_conditional_core ty

private unsafe def heuristic_simp_lemma_extraction (prf : expr) : tactic (List Name) :=
  prf.list_constant.toList.mfilter is_simp_lemma

/-- Checks whether two expressions are equal for the simplifier. That is,
they are reducibly-definitional equal, and they have the same head symbol. -/
unsafe def is_simp_eq (a b : expr) : tactic Bool :=
  if a.get_app_fn.const_name ≠ b.get_app_fn.const_name then pure false
  else succeeds <| is_def_eq a b Transparency.reducible

/-- Reports declarations that are simp lemmas whose left-hand side is not in simp-normal form. -/
unsafe def simp_nf_linter (timeout := 200000) (d : declaration) : tactic (Option Stringₓ) := do
  let tt ← is_simp_lemma d.to_name | pure none
  let-- Sometimes, a definition is tagged @[simp] to add the equational lemmas to the simp set.
    -- In this case, ignore the declaration if it is not a valid simp lemma by itself.
    tt
    ← is_valid_simp_lemma_cnst d.to_name | pure none
  let [] ← get_eqn_lemmas_for false d.to_name | pure none
  try_for timeout <|
      retrieve <| do
        let g ← mk_meta_var d
        set_goals [g]
        unfreezing intros
        let (lhs, rhs) ← target >>= simp_lhs_rhs
        let sls ← simp_lemmas.mk_default
        let sls' := sls [d]
        let (lhs', prf1, ns1) ←
          decorate_error "simplify fails on left-hand side:" <| simplify sls [] lhs { failIfUnchanged := ff }
        let prf1_lems ← heuristic_simp_lemma_extraction prf1
        if d ∈ prf1_lems then pure none
          else do
            let is_cond ← simp_is_conditional d
            let (rhs', prf2, ns2) ←
              decorate_error "simplify fails on right-hand side:" <| simplify sls [] rhs { failIfUnchanged := ff }
            let lhs'_eq_rhs' ← is_simp_eq lhs' rhs'
            let lhs_in_nf ← is_simp_eq lhs' lhs
            if lhs'_eq_rhs' then do
                let used_lemmas ← heuristic_simp_lemma_extraction (prf1 prf2)
                pure <|
                    pure <|
                      "simp can prove this:\n" ++ "  by simp only " ++ toString used_lemmas ++ "\n" ++
                          "One of the lemmas above could be a duplicate.\n" ++
                        "If that's not the case try reordering lemmas or adding @[priority].\n"
              else
                if ¬lhs_in_nf then do
                  let lhs ← pp lhs
                  let lhs' ← pp lhs'
                  pure <|
                      format.to_string <|
                        to_fmt "Left-hand side simplifies from" ++ lhs 2 ++ format.line ++ "to" ++ lhs' 2 ++
                                  format.line ++
                                "using " ++
                              (to_fmt prf1_lems).group.indent 2 ++
                            format.line ++
                          "Try to change the left-hand side to the simplified term!\n"
                else
                  if ¬is_cond ∧ lhs = lhs' then
                    pure <|
                      some <|
                        "Left-hand side does not simplify.\nYou need to debug this yourself using " ++
                          "`set_option trace.simplify.rewrite true`"
                  else pure none

library_note "simp-normal form"/--
This note gives you some tips to debug any errors that the simp-normal form linter raises.

The reason that a lemma was considered faulty is because its left-hand side is not in simp-normal
form.
These lemmas are hence never used by the simplifier.

This linter gives you a list of other simp lemmas: look at them!

Here are some tips depending on the error raised by the linter:

  1. 'the left-hand side reduces to XYZ':
     you should probably use XYZ as the left-hand side.

  2. 'simp can prove this':
     This typically means that lemma is a duplicate, or is shadowed by another lemma:

     2a. Always put more general lemmas after specific ones:
      ```
      @[simp] lemma zero_add_zero : 0 + 0 = 0 := rfl
      @[simp] lemma add_zero : x + 0 = x := rfl
      ```

      And not the other way around!  The simplifier always picks the last matching lemma.

     2b. You can also use `@[priority]` instead of moving simp-lemmas around in the file.

      Tip: the default priority is 1000.
      Use `@[priority 1100]` instead of moving a lemma down,
      and `@[priority 900]` instead of moving a lemma up.

     2c. Conditional simp lemmas are tried last. If they are shadowed
         just remove the `simp` attribute.

     2d. If two lemmas are duplicates, the linter will complain about the first one.
         Try to fix the second one instead!
         (You can find it among the other simp lemmas the linter prints out!)

  3. 'try_for tactic failed, timeout':
     This typically means that there is a loop of simp lemmas.
     Try to apply squeeze_simp to the right-hand side (removing this lemma from the simp set) to see
     what lemmas might be causing the loop.

     Another trick is to `set_option trace.simplify.rewrite true` and
     then apply `try_for 10000 { simp }` to the right-hand side.  You will
     see a periodic sequence of lemma applications in the trace message.
-/


/-- A linter for simp lemmas whose lhs is not in simp-normal form, and which hence never fire. -/
@[linter]
unsafe def linter.simp_nf : linter where
  test := simp_nf_linter
  auto_decls := true
  no_errors_found := "All left-hand sides of simp lemmas are in simp-normal form."
  errors_found :=
    "SOME SIMP LEMMAS ARE NOT IN SIMP-NORMAL FORM.\nsee note [simp-normal form] for tips how to debug this.\nhttps://leanprover-community.github.io/mathlib_docs/notes.html#simp-normal%20form"

private unsafe def simp_var_head (d : declaration) : tactic (Option Stringₓ) := do
  let tt ← is_simp_lemma d.to_name | pure none
  let-- Sometimes, a definition is tagged @[simp] to add the equational lemmas to the simp set.
    -- In this case, ignore the declaration if it is not a valid simp lemma by itself.
    tt
    ← is_valid_simp_lemma_cnst d.to_name | pure none
  let lhs ← simp_lhs d.type
  let head_sym@(expr.local_const _ _ _ _) ← pure lhs.get_app_fn | pure none
  let head_sym ← pp head_sym
  pure <| format.to_string <| "Left-hand side has variable as head symbol: " ++ head_sym

/-- A linter for simp lemmas whose lhs has a variable as head symbol,
and which hence never fire.
-/
@[linter]
unsafe def linter.simp_var_head : linter where
  test := simp_var_head
  auto_decls := true
  no_errors_found := "No left-hand sides of a simp lemma has a variable as head symbol."
  errors_found :=
    "LEFT-HAND SIDE HAS VARIABLE AS HEAD SYMBOL.\n" ++
      "Some simp lemmas have a variable as head symbol of the left-hand side:"

private unsafe def simp_comm (d : declaration) : tactic (Option Stringₓ) := do
  let tt ← is_simp_lemma d.to_name | pure none
  let-- Sometimes, a definition is tagged @[simp] to add the equational lemmas to the simp set.
    -- In this case, ignore the declaration if it is not a valid simp lemma by itself.
    tt
    ← is_valid_simp_lemma_cnst d.to_name | pure none
  let (lhs, rhs) ← simp_lhs_rhs d.type
  if lhs ≠ rhs then pure none
    else do
      let (lhs', rhs') ← Prod.snd <$> open_pis_metas d >>= simp_lhs_rhs
      let tt ← succeeds <| unify rhs lhs' transparency.reducible | pure none
      let tt ← succeeds <| is_def_eq rhs lhs' transparency.reducible | pure none
      let-- ensure that the second application makes progress:
        ff
        ← succeeds <| unify lhs' rhs' transparency.reducible | pure none
      pure <| "should not be marked simp"

/-- A linter for commutativity lemmas that are marked simp. -/
@[linter]
unsafe def linter.simp_comm : linter where
  test := simp_comm
  auto_decls := true
  no_errors_found := "No commutativity lemma is marked simp."
  errors_found := "COMMUTATIVITY LEMMA IS SIMP.\n" ++ "Some commutativity lemmas are simp lemmas:"

