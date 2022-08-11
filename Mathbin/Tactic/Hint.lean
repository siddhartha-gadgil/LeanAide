/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Tactic.SolveByElim
import Mathbin.Tactic.Interactive

namespace Tactic

namespace Hint

/-- An attribute marking a `tactic unit` or `tactic string` which should be used by the `hint`
tactic. -/
@[user_attribute]
unsafe def hint_tactic_attribute : user_attribute where
  Name := `hint_tactic
  descr := "A tactic that should be tried by `hint`."

add_tactic_doc
  { Name := "hint_tactic", category := DocCategory.attr, declNames := [`tactic.hint.hint_tactic_attribute],
    tags := ["rewrite", "search"] }

setup_tactic_parser

private unsafe def add_tactic_hint (n : Name) (t : expr) : tactic Unit := do
  add_decl <| declaration.defn n [] (quote.1 (tactic Stringₓ)) t ReducibilityHints.opaque ff
  hint_tactic_attribute n () tt

/-- `add_hint_tactic t` runs the tactic `t` whenever `hint` is invoked.
The typical use case is `add_hint_tactic "foo"` for some interactive tactic `foo`.
-/
@[user_command]
unsafe def add_hint_tactic (_ : parse (tk "add_hint_tactic")) : parser Unit := do
  let n ← parser.pexpr
  let e ← to_expr n
  let s ← eval_expr Stringₓ e
  let t := "`[" ++ s ++ "]"
  let (t, _) ← with_input parser.pexpr t
  of_tactic <| do
      let h := mkStrName s "_hint"
      let t ←
        to_expr
            (pquote.1 do
              %%ₓt
              pure (%%ₓn))
      add_tactic_hint h t

add_tactic_doc
  { Name := "add_hint_tactic", category := DocCategory.cmd, declNames := [`tactic.hint.add_hint_tactic],
    tags := ["search"] }

add_hint_tactic rfl

add_hint_tactic
  exact by
    decide

add_hint_tactic assumption

-- tidy does something better here: it suggests the actual "intros X Y f" string.
-- perhaps add a wrapper?
add_hint_tactic intro

add_hint_tactic infer_auto_param

add_hint_tactic dsimp'  at *

add_hint_tactic simp at *

-- TODO hook up to squeeze_simp?
add_hint_tactic fconstructor

add_hint_tactic injections_and_clear

add_hint_tactic solve_by_elim

add_hint_tactic unfold_coes

add_hint_tactic unfold_aux

end Hint

/-- Report a list of tactics that can make progress against the current goal,
and for each such tactic, the number of remaining goals afterwards.
-/
unsafe def hint : tactic (List (Stringₓ × ℕ)) := do
  let names ← attribute.get_instances `hint_tactic
  focus1 <| try_all_sorted (names name_to_tactic)

namespace Interactive

/-- Report a list of tactics that can make progress against the current goal.
-/
unsafe def hint : tactic Unit := do
  let hints ← tactic.hint
  if hints = 0 then fail "no hints available"
    else do
      let t ← hints 0
      if t.2 = 0 then do
          trace "the following tactics solve the goal:\n----"
          (hints fun p : Stringₓ × ℕ => p.2 = 0).mmap' fun p => tactic.trace f! "Try this: {p.1}"
        else do
          trace "the following tactics make progress:\n----"
          hints fun p => tactic.trace f! "Try this: {p.1}"

/-- `hint` lists possible tactics which will make progress (that is, not fail) against the current goal.

```lean
example {P Q : Prop} (p : P) (h : P → Q) : Q :=
begin
  hint,
  /- the following tactics make progress:
     ----
     Try this: solve_by_elim
     Try this: finish
     Try this: tauto
  -/
  solve_by_elim,
end
```

You can add a tactic to the list that `hint` tries by either using
1. `attribute [hint_tactic] my_tactic`, if `my_tactic` is already of type `tactic string`
(`tactic unit` is allowed too, in which case the printed string will be the name of the
tactic), or
2. `add_hint_tactic "my_tactic"`, specifying a string which works as an interactive tactic.
-/
add_tactic_doc
  { Name := "hint", category := DocCategory.tactic, declNames := [`tactic.interactive.hint],
    tags := ["search", "Try this"] }

end Interactive

end Tactic

