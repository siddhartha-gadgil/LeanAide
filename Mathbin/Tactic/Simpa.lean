/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Tactic.DocCommands

open Interactive

open Interactive.Types

namespace Tactic

namespace Interactive

open Expr Lean.Parser

-- mathport name: «expr ?»
local postfix:1024 "?" => optionalₓ

/-- This is a "finishing" tactic modification of `simp`. It has two forms.

* `simpa [rules, ...] using e` will simplify the goal and the type of
  `e` using `rules`, then try to close the goal using `e`.

  Simplifying the type of `e` makes it more likely to match the goal
  (which has also been simplified). This construction also tends to be
  more robust under changes to the simp lemma set.

* `simpa [rules, ...]` will simplify the goal and the type of a
  hypothesis `this` if present in the context, then try to close the goal using
  the `assumption` tactic. -/
unsafe def simpa (use_iota_eqn : parse <| (tk "!")?) (trace_lemmas : parse <| (tk "?")?) (no_dflt : parse only_flag)
    (hs : parse simp_arg_list) (attr_names : parse with_ident_list) (tgt : parse (tk "using" *> texpr)?)
    (cfg : simp_config_ext := {  }) : tactic Unit :=
  let simp_at (lc) (close_tac : tactic Unit) :=
    focus1 <|
      simp use_iota_eqn trace_lemmas no_dflt hs attr_names (Loc.ns lc) { cfg with failIfUnchanged := false } >>
        ((close_tac <|> trivialₓ) >> done <|> fail "simpa failed")
  match tgt with
  | none => get_local `this >> simp_at [some `this, none] assumption <|> simp_at [none] assumption
  | some e =>
    focus1 <| do
      let e ←
        i_to_expr e <|> do
            let ty ← target
            let e
              ←-- for positional error messages, we don't care about the result
                  i_to_expr_strict
                  (pquote.1 (%%ₓe : %%ₓty))
            let pty ← pp ty
            let ptgt ← pp e
            -- Fail deliberately, to advise regarding `simp; exact` usage
                fail
                ("simpa failed, 'using' expression type not directly " ++
                        "inferrable. Try:\n\nsimpa ... using\nshow " ++
                      to_fmt pty ++
                    ",\nfrom " ++
                  ptgt :
                  format)
      match e with
        | local_const _ lc _ _ => simp_at [some lc, none] (get_local lc >>= tactic.exact)
        | e => do
          let t ← infer_type e
          assertv `this t e
          simp_at [some `this, none] (get_local `this >>= tactic.exact)
          all_goals (try apply_instance)

add_tactic_doc
  { Name := "simpa", category := DocCategory.tactic, declNames := [`tactic.interactive.simpa],
    tags := ["simplification"] }

end Interactive

end Tactic

