/-
Copyright (c) 2017 Mario Carneiro All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import Mathbin.Tactic.Core

namespace Tactic

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- `copy_attribute' attr_name src tgt p d_name` copy (user) attribute `attr_name` from
   `src` to `tgt` if it is defined for `src`; unlike `copy_attribute` the primed version also copies
   the parameter of the user attribute, in the user attribute case. Make it persistent if `p` is
   `tt`; if `p` is `none`, the copied attribute is made persistent iff it is persistent on `src`  -/
unsafe def copy_attribute' (attr_name : Name) (src : Name) (tgt : Name) (p : Option Bool := none) : tactic Unit := do
  get_decl tgt <|>
      "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
  -- if the source doesn't have the attribute we do not error and simply return
        mwhen
        (succeeds (has_attribute attr_name src)) <|
      do
      let (p', prio) ← has_attribute attr_name src
      let p := p p'
      let s ← try_or_report_error (set_basic_attribute attr_name tgt p prio)
      let Sum.inr msg ← return s | skip
      if msg = (f! "set_basic_attribute tactic failed, '{attr_name}' is not a basic attribute").toString then do
          let user_attr_const ← get_user_attribute_name attr_name >>= mk_const
          let tac ←
            eval_pexpr (tactic Unit)
                (pquote.1
                  (user_attribute.get_param_untyped (%%ₓuser_attr_const) (%%ₓquote.1 src) >>= fun x =>
                    user_attribute.set_untyped (%%ₓuser_attr_const) (%%ₓquote.1 tgt) x (%%ₓquote.1 p)
                      (%%ₓquote.1 prio)))
          tac
        else fail msg

open Expr

/-- Auxilliary function for `additive_test`. The bool argument *only* matters when applied
to exactly a constant. -/
unsafe def additive_test_aux (f : Name → Option Name) (ignore : name_map <| List ℕ) : Bool → expr → Bool
  | b, var n => true
  | b, sort l => true
  | b, const n ls => b || (f n).isSome
  | b, mvar n m t => true
  | b, local_const n m bi t => true
  | b, app e f =>
    additive_test_aux true e &&-- this might be inefficient.
      -- If it becomes a performance problem: we can give this info for the recursive call to `e`.
      match ignore.find e.get_app_fn.const_name with
      | some l => if e.get_app_num_args + 1 ∈ l then true else additive_test_aux false f
      | none => additive_test_aux false f
  | b, lam n bi e t => additive_test_aux false t
  | b, pi n bi e t => additive_test_aux false t
  | b, elet n g e f => additive_test_aux false e && additive_test_aux false f
  | b, macro d args => true

/-- `additive_test f replace_all ignore e` tests whether the expression `e` contains no constant
`nm` that is not applied to any arguments, and such that `f nm = none`.
This is used in `@[to_additive]` for deciding which subexpressions to transform: we only transform
constants if `additive_test` applied to their first argument returns `tt`.
This means we will replace expression applied to e.g. `α` or `α × β`, but not when applied to
e.g. `ℕ` or `ℝ × α`.
`f` is the dictionary of declarations that are in the `to_additive` dictionary.
We ignore all arguments specified in the `name_map` `ignore`.
If `replace_all` is `tt` the test always return `tt`.
-/
unsafe def additive_test (f : Name → Option Name) (replace_all : Bool) (ignore : name_map <| List ℕ) (e : expr) :
    Bool :=
  if replace_all then true else additive_test_aux f ignore false e

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- transform the declaration `src` and all declarations `pre._proof_i` occurring in `src`
using the dictionary `f`.
`replace_all`, `trace`, `ignore` and `reorder` are configuration options.
`pre` is the declaration that got the `@[to_additive]` attribute and `tgt_pre` is the target of this
declaration. -/
unsafe def transform_decl_with_prefix_fun_aux (f : Name → Option Name) (replace_all trace : Bool)
    (relevant : name_map ℕ) (ignore reorder : name_map <| List ℕ) (pre tgt_pre : Name) : Name → Tactic Unit :=
  fun src => do
  let-- if this declaration is not `pre` or an internal declaration, we do nothing.
    tt
    ← return (src = pre ∨ src.is_internal : Bool) |
    if (f src).isSome then skip
      else
        "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
  let env ← get_env
  let-- we find the additive name of `src`
  tgt := src.mapPrefix fun n => if n = pre then some tgt_pre else none
  let-- we skip if we already transformed this declaration before
    ff
    ← return <| env.contains tgt | skip
  let decl ← get_decl src
  (-- we first transform all the declarations of the form `pre._proof_i`
          decl
          pre).mfold
      () fun n _ => transform_decl_with_prefix_fun_aux n
  (decl pre).mfold () fun n _ => transform_decl_with_prefix_fun_aux n
  let-- we transform `decl` using `f` and the configuration options.
  decl := decl.update_with_fun env (Name.mapPrefix f) (additive_test f replace_all ignore) relevant reorder tgt
  let pp_decl
    ←-- o ← get_options, set_options $ o.set_bool `pp.all tt, -- print with pp.all (for debugging)
        pp
        decl
  when trace <|
      ← do
        dbg_trace "[to_additive] > generating
          {← pp_decl}"
  decorate_error
        (f! "@[to_additive] failed. Type mismatch in additive declaration.
            For help, see the docstring of `to_additive.attr`, section `Troubleshooting`.
            Failed to add declaration
            {pp_decl}
            
            Nested error message:
            ").toString <|
      do
      if env src then add_protected_decl decl else add_decl decl
      -- we test that the declaration value type-checks, so that we get the decorated error message
            -- without this line, the type-checking might fail outside the `decorate_error`.
            decorate_error
            "proof doesn't type-check. " <|
          type_check decl

/-- Make a new copy of a declaration,
replacing fragments of the names of identifiers in the type and the body using the function `f`.
This is used to implement `@[to_additive]`.
-/
unsafe def transform_decl_with_prefix_fun (f : Name → Option Name) (replace_all trace : Bool) (relevant : name_map ℕ)
    (ignore reorder : name_map <| List ℕ) (src tgt : Name) (attrs : List Name) : Tactic Unit := do
  -- In order to ensure that attributes are copied correctly we must transform declarations and
      -- attributes in the right order:
      -- first generate the transformed main declaration
      transform_decl_with_prefix_fun_aux
      f replace_all trace relevant ignore reorder src tgt src
  let ls ← get_eqn_lemmas_for true src
  -- now transform all of the equational lemmas
      ls <|
      transform_decl_with_prefix_fun_aux f replace_all trace relevant ignore reorder src tgt
  -- copy attributes for the equational lemmas so that they know if they are refl lemmas
      ls
      fun src_eqn => do
      let tgt_eqn := src_eqn fun n => if n = src then some tgt else none
      attrs fun n => copy_attribute' n src_eqn tgt_eqn
  -- set the transformed equation lemmas as equation lemmas for the new declaration
      ls
      fun src_eqn => do
      let e ← get_env
      let tgt_eqn := src_eqn fun n => if n = src then some tgt else none
      set_env (e tgt_eqn)
  -- copy attributes for the main declaration, this needs the equational lemmas to exist already
      attrs
      fun n => copy_attribute' n src tgt

/-- Make a new copy of a declaration, replacing fragments of the names of identifiers in the type and
the body using the dictionary `dict`.
This is used to implement `@[to_additive]`.
-/
unsafe def transform_decl_with_prefix_dict (dict : name_map Name) (replace_all trace : Bool) (relevant : name_map ℕ)
    (ignore reorder : name_map <| List ℕ) (src tgt : Name) (attrs : List Name) : Tactic Unit :=
  transform_decl_with_prefix_fun dict.find replace_all trace relevant ignore reorder src tgt attrs

end Tactic

