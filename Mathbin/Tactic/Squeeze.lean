/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Control.Traversable.Basic
import Mathbin.Tactic.Simpa

setup_tactic_parser

private unsafe def loc.to_string_aux : Option Name → Stringₓ
  | none => "⊢"
  | some x => toString x

/-- pretty print a `loc` -/
unsafe def loc.to_string : Loc → Stringₓ
  | loc.ns [] => ""
  | loc.ns [none] => ""
  | loc.ns ls => Stringₓ.join <| List.intersperse " " (" at" :: ls.map loc.to_string_aux)
  | loc.wildcard => " at *"

/-- shift `pos` `n` columns to the left -/
unsafe def pos.move_left (p : Pos) (n : ℕ) : Pos where
  line := p.line
  column := p.column - n

namespace Tactic

deriving instance DecidableEq for simp_arg_type

/-- Turn a `simp_arg_type` into a string. -/
unsafe instance simp_arg_type.has_to_string : HasToString simp_arg_type :=
  ⟨fun a =>
    match a with
    | simp_arg_type.all_hyps => "*"
    | simp_arg_type.except n => "-" ++ toString n
    | simp_arg_type.expr e => toString e
    | simp_arg_type.symm_expr e => "←" ++ toString e⟩

open List

/-- parse structure instance of the shape `{ field1 := value1, .. , field2 := value2 }` -/
unsafe def struct_inst : lean.parser pexpr :=
  with_desc "cfg" <| do
    tk "{"
    let ls ←
      sep_by (skip_info (tk ","))
          (Sum.inl <$> (tk ".." *> texpr) <|> Sum.inr <$> (Prod.mk <$> ident <* tk ":=" <*> texpr))
    tk "}"
    let (srcs, fields) := partitionMap id ls
    let (names, values) := unzip fields
    pure <| pexpr.mk_structure_instance { field_names := names, field_values := values, sources := srcs }

/-- pretty print structure instance -/
unsafe def struct.to_tactic_format (e : pexpr) : tactic format := do
  let r ← e.get_structure_instance_info
  let fs ←
    mzipWith
        (fun n v => do
          let v ← to_expr v >>= pp
          pure <| f! "{n } := {v}")
        r.field_names r.field_values
  let ss := r.sources.map fun s => f! " .. {s}"
  let x : format := format.join <| List.intersperse ", " (fs ++ ss)
  pure f! " \{{x}}}"

/-- Attribute containing a table that accumulates multiple `squeeze_simp` suggestions -/
@[user_attribute]
private unsafe def squeeze_loc_attr :
    user_attribute Unit (Option (List (Pos × Stringₓ × List simp_arg_type × Stringₓ))) where
  Name := `_squeeze_loc
  parser := fail "this attribute should not be used"
  descr := "table to accumulate multiple `squeeze_simp` suggestions"

/-- dummy declaration used as target of `squeeze_loc` attribute -/
def squeezeLocAttrCarrier :=
  ()

run_cmd
  squeeze_loc_attr.Set `` squeeze_loc_attr_carrier none true

/-- Format a list of arguments for use with `simp` and friends. This omits the
list entirely if it is empty.

Patch: `pp` was changed to `to_string` because it was getting rid of prefixes
that would be necessary for some disambiguations. -/
unsafe def render_simp_arg_list : List simp_arg_type → format
  | [] => ""
  | args => (· ++ ·) " " <| to_line_wrap_format <| args.map toString

/-- Emit a suggestion to the user. If inside a `squeeze_scope` block,
the suggestions emitted through `mk_suggestion` will be aggregated so that
every tactic that makes a suggestion can consider multiple execution of the
same invocation.
If `at_pos` is true, make the suggestion at `p` instead of the current position. -/
unsafe def mk_suggestion (p : Pos) (pre post : Stringₓ) (args : List simp_arg_type) (at_pos := false) : tactic Unit :=
  do
  let xs ← squeeze_loc_attr.get_param `` squeeze_loc_attr_carrier
  match xs with
    | none => do
      let args := render_simp_arg_list args
      if at_pos then (@scopeTrace _ p p) fun _ => _root_.trace (s! "{pre }{args }{post}") (pure () : tactic Unit)
        else trace s! "{pre }{args }{post}"
    | some xs => do
      squeeze_loc_attr `` squeeze_loc_attr_carrier ((p, pre, args, post) :: xs) ff

/-- translate a `pexpr` into a `simp` configuration -/
unsafe def parse_config : Option pexpr → tactic (simp_config_ext × format)
  | none => pure ({  }, "")
  | some cfg => do
    let e ← to_expr (pquote.1 (%%ₓcfg : simp_config_ext))
    let fmt ← has_to_tactic_format.to_tactic_format cfg
    Prod.mk <$> eval_expr simp_config_ext e <*> struct.to_tactic_format cfg

/-- translate a `pexpr` into a `dsimp` configuration -/
unsafe def parse_dsimp_config : Option pexpr → tactic (dsimp_config × format)
  | none => pure ({  }, "")
  | some cfg => do
    let e ← to_expr (pquote.1 (%%ₓcfg : simp_config_ext))
    let fmt ← has_to_tactic_format.to_tactic_format cfg
    Prod.mk <$> eval_expr dsimp_config e <*> struct.to_tactic_format cfg

/-- `same_result proof tac` runs tactic `tac` and checks if the proof
produced by `tac` is equivalent to `proof`. -/
unsafe def same_result (pr : proof_state) (tac : tactic Unit) : tactic Bool := do
  let s ← get_proof_state_after tac
  pure <| some pr = s

/-- Consumes the first list of `simp` arguments, accumulating required arguments
on the second one and unnecessary arguments on the third one.
-/
private unsafe def filter_simp_set_aux (tac : Bool → List simp_arg_type → tactic Unit) (args : List simp_arg_type)
    (pr : proof_state) :
    List simp_arg_type → List simp_arg_type → List simp_arg_type → tactic (List simp_arg_type × List simp_arg_type)
  | [], ys, ds => pure (ys, ds)
  | x :: xs, ys, ds => do
    let b ← same_result pr (tac true (args ++ xs ++ ys))
    if b then filter_simp_set_aux xs ys (ds x) else filter_simp_set_aux xs (ys x) ds

initialize
  registerTraceClass.1 `squeeze.deleted

/-- `filter_simp_set g call_simp user_args simp_args` returns `args'` such that, when calling
`call_simp tt /- only -/ args'` on the goal `g` (`g` is a meta var) we end up in the same
state as if we had called `call_simp ff (user_args ++ simp_args)` and removing any one
element of `args'` changes the resulting proof.
-/
unsafe def filter_simp_set (tac : Bool → List simp_arg_type → tactic Unit) (user_args simp_args : List simp_arg_type) :
    tactic (List simp_arg_type) := do
  let some s ← get_proof_state_after (tac false (user_args ++ simp_args))
  let (simp_args', _) ← filter_simp_set_aux tac user_args s simp_args [] []
  let (user_args', ds) ← filter_simp_set_aux tac simp_args' s user_args [] []
  when (is_trace_enabled_for `squeeze.deleted = tt ∧ ¬ds)
      (← do
        dbg_trace "deleting provided arguments {← ds}")
  pure (user_args' ++ simp_args')

/-- make a `simp_arg_type` that references the name given as an argument -/
unsafe def name.to_simp_args (n : Name) : simp_arg_type :=
  simp_arg_type.expr <| @expr.local_const false n n default pexpr.mk_placeholder

/-- If the `name` is (likely) to be overloaded, then prepend a `_root_` on it. The `expr` of an
overloaded name is constructed using `expr.macro`; this is how we guess whether it's overloaded. -/
unsafe def prepend_root_if_needed (n : Name) : tactic Name := do
  let x ← resolve_name' n
  return <|
      match x with
      | expr.macro _ _ => `_root_ ++ n
      | _ => n

/-- tactic combinator to create a `simp`-like tactic that minimizes its
argument list.

 * `slow`: adds all rfl-lemmas from the environment to the initial list (this is a slower but more
           accurate strategy)
 * `no_dflt`: did the user use the `only` keyword?
 * `args`:    list of `simp` arguments
 * `tac`:     how to invoke the underlying `simp` tactic
-/
unsafe def squeeze_simp_core (slow no_dflt : Bool) (args : List simp_arg_type)
    (tac : ∀ (no_dflt : Bool) (args : List simp_arg_type), tactic Unit)
    (mk_suggestion : List simp_arg_type → tactic Unit) : tactic Unit := do
  let v ← target >>= mk_meta_var
  let args ←
    if slow then do
        let simp_set ← attribute.get_instances `simp
        let simp_set ← simp_set.mfilter <| has_attribute' `_refl_lemma
        let simp_set ← simp_set.mmap <| resolve_name' >=> pure ∘ simp_arg_type.expr
        pure <| args ++ simp_set
      else pure args
  let g ←
    retrieve <| do
        let g ← main_goal
        tac no_dflt args
        instantiate_mvars g
  let vs := g.list_constant'
  let vs ← vs.mfilter is_simp_lemma
  let vs ← vs.mmap strip_prefix
  let vs ← vs.mmap prepend_root_if_needed
  with_local_goals' [v] (filter_simp_set tac args <| vs name.to_simp_args) >>= mk_suggestion
  tac no_dflt args

namespace Interactive

/-- combinator meant to aggregate the suggestions issued by multiple calls
of `squeeze_simp` (due, for instance, to `;`).

Can be used as:

```lean
example {α β} (xs ys : list α) (f : α → β) :
  (xs ++ ys.tail).map f = xs.map f ∧ (xs.tail.map f).length = xs.length :=
begin
  have : xs = ys, admit,
  squeeze_scope
  { split; squeeze_simp,
    -- `squeeze_simp` is run twice, the first one requires
    -- `list.map_append` and the second one
    -- `[list.length_map, list.length_tail]`
    -- prints only one message and combine the suggestions:
    -- > Try this: simp only [list.length_map, list.length_tail, list.map_append]
    squeeze_simp [this]
    -- `squeeze_simp` is run only once
    -- prints:
    -- > Try this: simp only [this] },
end
```

-/
unsafe def squeeze_scope (tac : itactic) : tactic Unit := do
  let none ← squeeze_loc_attr.get_param `` squeeze_loc_attr_carrier | pure ()
  squeeze_loc_attr `` squeeze_loc_attr_carrier (some []) ff
  finally tac <| do
      let some xs ← squeeze_loc_attr `` squeeze_loc_attr_carrier | fail "invalid state"
      let m := native.rb_lmap.of_list xs
      squeeze_loc_attr `` squeeze_loc_attr_carrier none ff
      m fun ⟨p, suggs⟩ => do
          let ⟨pre, _, post⟩ := suggs
          let suggs : List (List simp_arg_type) := suggs <| Prod.fst ∘ Prod.snd
          mk_suggestion p pre post (suggs List.unionₓ []) tt
          pure ()

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- `squeeze_simp`, `squeeze_simpa` and `squeeze_dsimp` perform the same
task with the difference that `squeeze_simp` relates to `simp` while
`squeeze_simpa` relates to `simpa` and `squeeze_dsimp` relates to
`dsimp`. The following applies to `squeeze_simp`, `squeeze_simpa` and
`squeeze_dsimp`.

`squeeze_simp` behaves like `simp` (including all its arguments)
and prints a `simp only` invocation to skip the search through the
`simp` lemma list.

For instance, the following is easily solved with `simp`:

```lean
example : 0 + 1 = 1 + 0 := by simp
```

To guide the proof search and speed it up, we may replace `simp`
with `squeeze_simp`:

```lean
example : 0 + 1 = 1 + 0 := by squeeze_simp
-- prints:
-- Try this: simp only [add_zero, eq_self_iff_true, zero_add]
```

`squeeze_simp` suggests a replacement which we can use instead of
`squeeze_simp`.

```lean
example : 0 + 1 = 1 + 0 := by simp only [add_zero, eq_self_iff_true, zero_add]
```

`squeeze_simp only` prints nothing as it already skips the `simp` list.

This tactic is useful for speeding up the compilation of a complete file.
Steps:

   1. search and replace ` simp` with ` squeeze_simp` (the space helps avoid the
      replacement of `simp` in `@[simp]`) throughout the file.
   2. Starting at the beginning of the file, go to each printout in turn, copy
      the suggestion in place of `squeeze_simp`.
   3. after all the suggestions were applied, search and replace `squeeze_simp` with
      `simp` to remove the occurrences of `squeeze_simp` that did not produce a suggestion.

Known limitation(s):
  * in cases where `squeeze_simp` is used after a `;` (e.g. `cases x; squeeze_simp`),
    `squeeze_simp` will produce as many suggestions as the number of goals it is applied to.
    It is likely that none of the suggestion is a good replacement but they can all be
    combined by concatenating their list of lemmas. `squeeze_scope` can be used to
    combine the suggestions: `by squeeze_scope { cases x; squeeze_simp }`
  * sometimes, `simp` lemmas are also `_refl_lemma` and they can be used without appearing in the
    resulting proof. `squeeze_simp` won't know to try that lemma unless it is called as
    `squeeze_simp?`
-/
unsafe def squeeze_simp (key : parse cur_pos) (slow_and_accurate : parse («expr ?» (tk "?")))
    (use_iota_eqn : parse («expr ?» (tk "!"))) (no_dflt : parse only_flag) (hs : parse simp_arg_list)
    (attr_names : parse with_ident_list) (locat : parse location) (cfg : parse («expr ?» struct_inst)) : tactic Unit :=
  do
  let (cfg', c) ← parse_config cfg
  squeeze_simp_core slow_and_accurate no_dflt hs
      (fun l_no_dft l_args => simp use_iota_eqn none l_no_dft l_args attr_names locat cfg') fun args =>
      let use_iota_eqn := if use_iota_eqn then "!" else ""
      let attrs := if attr_names then "" else Stringₓ.join (List.intersperse " " (" with" :: attr_names toString))
      let loc := loc.to_string locat
      mk_suggestion (key 1) (s! "Try this: simp{use_iota_eqn} only") (s! "{attrs }{loc }{c}") args

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- see `squeeze_simp` -/
unsafe def squeeze_simpa (key : parse cur_pos) (slow_and_accurate : parse («expr ?» (tk "?")))
    (use_iota_eqn : parse («expr ?» (tk "!"))) (no_dflt : parse only_flag) (hs : parse simp_arg_list)
    (attr_names : parse with_ident_list) (tgt : parse («expr ?» (tk "using" *> texpr)))
    (cfg : parse («expr ?» struct_inst)) : tactic Unit := do
  let (cfg', c) ← parse_config cfg
  let tgt' ←
    traverse
        (fun t => do
          let t ← to_expr t >>= pp
          pure f! " using {t}")
        tgt
  squeeze_simp_core slow_and_accurate no_dflt hs
      (fun l_no_dft l_args => simpa use_iota_eqn none l_no_dft l_args attr_names tgt cfg') fun args =>
      let use_iota_eqn := if use_iota_eqn then "!" else ""
      let attrs := if attr_names then "" else Stringₓ.join (List.intersperse " " (" with" :: attr_names toString))
      let tgt' := tgt' ""
      mk_suggestion (key 1) (s! "Try this: simpa{use_iota_eqn} only") (s! "{attrs }{tgt' }{c}") args

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- `squeeze_dsimp` behaves like `dsimp` (including all its arguments)
and prints a `dsimp only` invocation to skip the search through the
`simp` lemma list. See the doc string of `squeeze_simp` for examples.
 -/
unsafe def squeeze_dsimp (key : parse cur_pos) (slow_and_accurate : parse («expr ?» (tk "?")))
    (use_iota_eqn : parse («expr ?» (tk "!"))) (no_dflt : parse only_flag) (hs : parse simp_arg_list)
    (attr_names : parse with_ident_list) (locat : parse location) (cfg : parse («expr ?» struct_inst)) : tactic Unit :=
  do
  let (cfg', c) ← parse_dsimp_config cfg
  squeeze_simp_core slow_and_accurate no_dflt hs (fun l_no_dft l_args => dsimp l_no_dft l_args attr_names locat cfg')
      fun args =>
      let use_iota_eqn := if use_iota_eqn then "!" else ""
      let attrs := if attr_names then "" else Stringₓ.join (List.intersperse " " (" with" :: attr_names toString))
      let loc := loc.to_string locat
      mk_suggestion (key 1) (s! "Try this: dsimp{use_iota_eqn} only") (s! "{attrs }{loc }{c}") args

end Interactive

end Tactic

open Tactic.Interactive

add_tactic_doc
  { Name := "squeeze_simp / squeeze_simpa / squeeze_dsimp / squeeze_scope", category := DocCategory.tactic,
    declNames := [`` squeeze_simp, `` squeeze_dsimp, `` squeeze_simpa, `` squeeze_scope],
    tags := ["simplification", "Try this"], inheritDescriptionFrom := `` squeeze_simp }

