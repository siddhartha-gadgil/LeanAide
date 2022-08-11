/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Damiano Testa
-/
import Mathbin.Tactic.Interactive

/-! `congrm`: `congr` with pattern-matching

`congrm e` gives to the use the functionality of using `congr` with an expression `e` "guiding"
`congr` through the matching.  This allows more flexibility than `congr' n`, which enters uniformly
through `n` iterations.  Instead, we can guide the matching deeper on some parts of the expression
and stop earlier on other parts.
-/


namespace Tactic

/-- For each element of `list congr_arg_kind` that is `eq`, add a pair `(g, pat)` to the
final list.  Otherwise, discard an appropriate number of initial terms from each list
(possibly none from the first) and repeat.

`pat` is the given pattern-piece at the appropriate location, extracted from the last `list expr`.
It appears to be the list of arguments of a function application.

`g` is possibly the proof of an equality?  It is extracted from the first `list expr`.
-/
private unsafe def extract_subgoals : List expr → List CongrArgKind → List expr → tactic (List (expr × expr))
  | _ :: _ :: g :: prf_args, CongrArgKind.eq :: kinds, pat :: pat_args =>
    (fun rest => (g, pat) :: rest) <$> extract_subgoals prf_args kinds pat_args
  | _ :: prf_args, CongrArgKind.fixed :: kinds, _ :: pat_args => extract_subgoals prf_args kinds pat_args
  | prf_args, CongrArgKind.fixed_no_param :: kinds, _ :: pat_args => extract_subgoals prf_args kinds pat_args
  | _ :: _ :: prf_args, CongrArgKind.cast :: kinds, _ :: pat_args => extract_subgoals prf_args kinds pat_args
  | _, _, [] => pure []
  | _, _, _ => fail "unsupported congr lemma"

/-- `equate_with_pattern_core pat` solves a single goal of the form `lhs = rhs`
(assuming that `lhs` and `rhs` are unifiable with `pat`)
by applying congruence lemmas until `pat` is a metavariable.
Returns the list of metavariables for the new subgoals at the leafs.
Calls `set_goals []` at the end.
-/
unsafe def equate_with_pattern_core : expr → tactic (List expr)
  | pat =>
    applyc `` Subsingleton.elimₓ >> pure [] <|>
      applyc `` rfl >> pure [] <|>
        if pat.is_mvar || pat.get_delayed_abstraction_locals.isSome then do
          try <| applyc `` _root_.propext
          get_goals <* set_goals []
        else
          match pat with
          | expr.app _ _ => do
            let cl ← mk_specialized_congr_lemma pat
            let H_congr_lemma ← assertv `H_congr_lemma cl.type cl.proof
            let [prf] ← get_goals
            apply H_congr_lemma <|> fail "could not apply congr_lemma"
            all_goals' <| try <| clear H_congr_lemma
            -- given the `set_goals []` that follows, is this needed?
                set_goals
                []
            let prf ← instantiate_mvars prf
            let subgoals ← extract_subgoals prf.get_app_args cl.arg_kinds pat.get_app_args
            let subgoals ←
              subgoals.mmap fun ⟨subgoal, subpat⟩ => do
                  set_goals [subgoal]
                  equate_with_pattern_core subpat
            pure subgoals
          | expr.lam _ _ _ body => do
            applyc `` _root_.funext
            let x ← intro pat.binding_name
            equate_with_pattern_core <| body x
          | expr.pi _ _ _ codomain => do
            applyc `` _root_.pi_congr
            let x ← intro pat.binding_name
            equate_with_pattern_core <| codomain x
          | _ => do
            let pat ← pp pat
            fail <| to_fmt "unsupported pattern:\n" ++ pat

/-- `equate_with_pattern pat` solves a single goal of the form `lhs = rhs`
(assuming that `lhs` and `rhs` are unifiable with `pat`)
by applying congruence lemmas until `pat` is a metavariable.
The subgoals for the leafs are prepended to the goals.
--/
unsafe def equate_with_pattern (pat : expr) : tactic Unit := do
  let congr_subgoals ← solve1 (equate_with_pattern_core pat)
  let gs ← get_goals
  set_goals <| congr_subgoals ++ gs

end Tactic

namespace Tactic.Interactive

open Tactic Interactive

setup_tactic_parser

/-- Assume that the goal is of the form `lhs = rhs` or `lhs ↔ rhs`.
`congrm e` takes an expression `e` containing placeholders `_` and scans `e, lhs, rhs` in parallel.

It matches both `lhs` and `rhs` to the pattern `e`, and produces one goal for each placeholder,
stating that the corresponding subexpressions in `lhs` and `rhs` are equal.

Examples:
```lean
example {a b c d : ℕ} :
  nat.pred a.succ * (d + (c + a.pred)) = nat.pred b.succ * (b + (c + d.pred)) :=
begin
  congrm nat.pred (nat.succ _) * (_ + _),
/-  Goals left:
⊢ a = b
⊢ d = b
⊢ c + a.pred = c + d.pred
-/
  sorry,
  sorry,
  sorry,
end

example {a b : ℕ} (h : a = b) : (λ y : ℕ, ∀ z, a + a = z) = (λ x, ∀ z, b + a = z) :=
begin
  congrm λ x, ∀ w, _ + a = w,
  -- produces one goal for the underscore: ⊢ a = b
  exact h,
end
```
-/
unsafe def congrm (arg : parse texpr) : tactic Unit := do
  try <| applyc `` _root_.eq.to_iff
  let quote.1 (@Eq (%%ₓty) _ _) ← target | fail "congrm: goal must be an equality or iff"
  let ta ← to_expr (pquote.1 (%%ₓarg : %%ₓty)) true false
  equate_with_pattern ta

add_tactic_doc
  { Name := "congrm", category := DocCategory.tactic, declNames := [`tactic.interactive.congrm],
    tags := ["congruence"] }

end Tactic.Interactive

