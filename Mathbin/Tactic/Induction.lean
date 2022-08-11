/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Mathbin.Tactic.Clear
import Mathbin.Tactic.Dependencies
import Mathbin.Tactic.FreshNames
import Mathbin.Tactic.Generalizes
import Mathbin.Tactic.HasVariableNames
import Mathbin.Tactic.UnifyEquations

/-!
# A better tactic for induction and case analysis

This module defines the tactics `tactic.interactive.induction'` and
`tactic.interactive.cases'`, which are variations on Lean's builtin `induction`
and `cases`. The primed variants feature various improvements over the builtin
tactics; in particular, they generate more human-friendly names and `induction'`
deals much better with indexed inductive types. See the tactics' documentation
for more details. We also provide corresponding non-interactive induction
tactics `tactic.eliminate_hyp` and `tactic.eliminate_expr`.

The design and implementation of these tactics is described in a
[draft paper](https://limperg.de/paper/cpp2021-induction/).
-/


open Expr Native

open Tactic.Interactive (case_tag.from_tag_hyps)

namespace Tactic

namespace Eliminate

/-!
## Tracing

We set up two tracing functions to be used by `eliminate_hyp` and its supporting
tactics. Their output is enabled by setting `trace.eliminate_hyp` to `true`.
-/


initialize
  registerTraceClass.1 `eliminate_hyp

/-- `trace_eliminate_hyp msg` traces `msg` if the option `trace.eliminate_hyp` is
`true`.
-/
unsafe def trace_eliminate_hyp {α} [has_to_format α] (msg : Thunkₓ α) : tactic Unit :=
  when_tracing `eliminate_hyp <| trace <| to_fmt "eliminate_hyp: " ++ to_fmt (msg ())

/-- `trace_state_eliminate_hyp msg` traces `msg` followed by the tactic state if the
option `trace.eliminate_hyp` is `true`.
-/
unsafe def trace_state_eliminate_hyp {α} [has_to_format α] (msg : Thunkₓ α) : tactic Unit := do
  let state ← read
  trace_eliminate_hyp <| format.join [to_fmt (msg ()), "\n-----\n", to_fmt State, "\n-----"]

/-!
## Information Gathering

We define data structures for information relevant to the induction, and
functions to collect this information for a specific goal.
-/


/-- Information about a constructor argument. E.g. given the declaration

```
induction ℕ : Type
| zero : ℕ
| suc (n : ℕ) : ℕ
```

the `zero` constructor has no arguments and the `suc` constructor has one
argument, `n`.

We record the following information:

- `aname`: the argument's name. If the argument was not explicitly named in the
  declaration, the elaborator generates a name for it.
- `type` : the argument's type.
- `dependent`: whether the argument is dependent, i.e. whether it occurs in the
  remainder of the constructor type.
- `index_occurrences`: the index arguments of the constructor's return type
  in which this argument occurs. If the constructor return type is
  `I i₀ ... iₙ` and the argument under consideration is `a`, and `a` occurs in
  `i₁` and `i₂`, then the `index_occurrences` are `1, 2`. As an additional
  requirement, for `iⱼ` to be considered an index occurrences,
  the type of `iⱼ` must match that of `a` according to
  `index_occurrence_type_match`.
- `recursive_leading_pis`: `none` if this constructor is not recursive.
  Otherwise, the argument has type `Π (x₁ : T₁) ... (xₙ : Tₙ), I ...`
  where `I` is the inductive type to which this constructor belongs. In this
  case, `recursive_leading_pis` is `some n` with `n` the number of leading Π
  binders in the argument's type.
-/
unsafe structure constructor_argument_info where
  aname : Name
  type : expr
  dependent : Bool
  index_occurrences : List ℕ
  recursive_leading_pis : Option ℕ
  deriving has_reflect

namespace ConstructorArgumentInfo

/-- `is_recursive c` is true iff the constructor argument described by `c` is
recursive.
-/
unsafe def is_recursive (c : constructor_argument_info) :=
  c.recursive_leading_pis.isSome

end ConstructorArgumentInfo

/-- Information about a constructor. Contains:

- `cname`: the constructor's name.
- `non_param_args`: information about the arguments of the constructor,
  excluding the arguments induced by the parameters of the inductive type.
- `num_non_param_args`: the length of `non_param_args`.
- `rec_args`: the subset of `non_param_args` which are recursive constructor
  arguments.
- `num_rec_args`: the length of `rec_args`.

For example, take the constructor
```
list.cons : ∀ {α} (x : α) (xs : list α), list α
```
`α` is a parameter of `list`, so `non_param_args` contains information about `x`
and `xs`. `rec_args` contains information about `xs`.
-/
unsafe structure constructor_info where
  cname : Name
  non_param_args : List constructor_argument_info
  num_non_param_args : ℕ
  rec_args : List constructor_argument_info
  num_rec_args : ℕ
  deriving has_reflect

/-- When we construct the goal for the minor premise of a given constructor, this is
the number of hypotheses we must name.
-/
unsafe def constructor_info.num_nameable_hypotheses (c : constructor_info) : ℕ :=
  c.num_non_param_args + c.num_rec_args

/-- Information about an inductive type. Contains:

- `iname`: the type's name.
- `constructors`: information about the type's constructors.
- `num_constructors`: the length of `constructors`.
- `type`: the type's type.
- `num_param`: the type's number of parameters.
- `num_indices`: the type's number of indices.
-/
unsafe structure inductive_info where
  iname : Name
  constructors : List constructor_info
  num_constructors : ℕ
  type : expr
  num_params : ℕ
  num_indices : ℕ
  deriving has_reflect

/-- Information about a major premise (i.e. the hypothesis on which we are
performing induction). Contains:

- `mpname`: the major premise's name.
- `mpexpr`: the major premise itself.
- `type`: the type of `mpexpr`.
- `args`: the arguments of the major premise. The major premise has type
  `I x₀ ... xₙ`, where `I` is an inductive type. `args` is the map
  `[0 → x₀, ..., n → xₙ]`.
-/
unsafe structure major_premise_info where
  mpname : Name
  mpexpr : expr
  type : expr
  args : rb_map ℕ expr

/-- `index_occurrence_type_match t s` is true iff `t` and `s` are definitionally
equal.
-/
-- We could extend this check to be more permissive. E.g. if a constructor
-- argument has type `list α` and the index has type `list β`, we may want to
-- consider these types sufficiently similar to inherit the name. Same (but even
-- more obvious) with `vec α n` and `vec α (n + 1)`.
unsafe def index_occurrence_type_match (t s : expr) : tactic Bool :=
  succeeds <| is_def_eq t s

/-- From the return type of a constructor `C` of an inductive type `I`, determine
the index occurrences of the constructor arguments of `C`.

Input:

- `num_params:` the number of parameters of `I`.
- `ret_type`: the return type of `C`. `e` must be of the form `I x₁ ... xₙ`.

Output: A map associating each local constant `c` that appears in any of the `xᵢ`
with the set of indexes `j` such that `c` appears in `xⱼ` and `xⱼ`'s type
matches that of `c` according to `tactic.index_occurrence_type_match`.
-/
unsafe def get_index_occurrences (num_params : ℕ) (ret_type : expr) : tactic (rb_lmap expr ℕ) := do
  let ret_args ← get_app_args_whnf ret_type
  ret_args
      (fun i occ_map ret_arg => do
        if i < num_params then pure occ_map
          else do
            let ret_arg_consts := ret_arg
            (ret_arg_consts occ_map) fun c occ_map => do
                let ret_arg_type ← infer_type ret_arg
                let eq ← index_occurrence_type_match c ret_arg_type
                pure <| if Eq then occ_map c i else occ_map)
      mk_rb_map

/-- `match_recursive_constructor_arg I T`, given `I` the name of an inductive type
and `T` the type of an argument of a constructor of `I`, returns `none` if the
argument is non-recursive (i.e. `I` does not appear in `T`). If the argument is
recursive, `T` is of the form `Π (x₁ : T₁) ... (xₙ : Tₙ), I ...`, in which case
`match_recursive_constructor_arg` returns `some n`. Matching is performed up to
WHNF with semireducible transparency.
-/
unsafe def match_recursive_constructor_arg (I : Name) (T : expr) : tactic (Option ℕ) := do
  let (pis, base) ← open_pis_whnf T
  let base ← get_app_fn_whnf base
  pure <|
      match base with
      | const c _ => if c = I then some pis else none
      | _ => none

/-- Get information about the arguments of a constructor `C` of an inductive type
`I`.

Input:

- `inductive_name`: the name of `I`.
- `num_params`: the number of parameters of `I`.
- `T`: the type of `C`.

Output: a `constructor_argument_info` structure for each argument of `C`.
-/
unsafe def get_constructor_argument_info (inductive_name : Name) (num_params : ℕ) (T : expr) :
    tactic (List constructor_argument_info) := do
  let ⟨args, ret⟩ ← open_pis_whnf_dep T
  let index_occs ← get_index_occurrences num_params ret
  args fun ⟨c, dep⟩ => do
      let occs := rb_set.of_list <| index_occs c
      let type := c
      let recursive_leading_pis ← match_recursive_constructor_arg inductive_name type
      pure ⟨c, type, dep, occs, recursive_leading_pis⟩

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Get information about a constructor `C` of an inductive type `I`.

Input:

- `iname`: the name of `I`.
- `num_params`: the number of parameters of `I`.
- `c` : the name of `C`.

Output:

A `constructor_info` structure for `C`.
-/
unsafe def get_constructor_info (iname : Name) (num_params : ℕ) (c : Name) : tactic constructor_info := do
  let env ← get_env
  when ¬env c <|
      "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
  let decl ← env.get c
  let args ← get_constructor_argument_info iname num_params decl.type
  let non_param_args := args.drop num_params
  let rec_args := non_param_args.filter fun ainfo => ainfo.is_recursive
  pure { cname := decl, non_param_args, num_non_param_args := non_param_args, rec_args, num_rec_args := rec_args }

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Get information about an inductive type `I`, given `I`'s name.
-/
unsafe def get_inductive_info (I : Name) : tactic inductive_info := do
  let env ← get_env
  when ¬env I <|
      "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
  let decl ← env.get I
  let type := decl.type
  let num_params := env.inductive_num_params I
  let num_indices := env.inductive_num_indices I
  let constructor_names := env.constructors_of I
  let constructors ← constructor_names.mmap (get_constructor_info I num_params)
  pure { iname := I, constructors, num_constructors := constructors, type, num_params, num_indices }

/-- Get information about a major premise. The given `expr` must be a local
hypothesis.
-/
unsafe def get_major_premise_info (major_premise : expr) : tactic major_premise_info := do
  let type ← infer_type major_premise
  let ⟨f, args⟩ ← get_app_fn_args_whnf type
  pure { mpname := major_premise, mpexpr := major_premise, type, args }

/-!
## Constructor Argument Naming

We define the algorithm for naming constructor arguments (which is a remarkably
big part of the tactic).
-/


/-- Information used when naming a constructor argument.
-/
unsafe structure constructor_argument_naming_info where
  mpinfo : major_premise_info
  iinfo : inductive_info
  cinfo : constructor_info
  ainfo : constructor_argument_info

/-- A constructor argument naming rule takes a `constructor_argument_naming_info`
structure and returns a list of suitable names for the argument. If the rule is
not applicable to the given constructor argument, the returned list is empty.
-/
@[reducible]
unsafe def constructor_argument_naming_rule : Type :=
  constructor_argument_naming_info → tactic (List Name)

/-- Naming rule for recursive constructor arguments.
-/
unsafe def constructor_argument_naming_rule_rec : constructor_argument_naming_rule := fun i =>
  pure <| if i.ainfo.is_recursive then [i.mpinfo.mpname] else []

/-- Naming rule for constructor arguments associated with an index.
-/
unsafe def constructor_argument_naming_rule_index : constructor_argument_naming_rule := fun i =>
  let index_occs := i.ainfo.index_occurrences
  let major_premise_args := i.mpinfo.args
  let get_major_premise_arg_local_names : ℕ → Option (Name × Name) := fun i => do
    let arg ← major_premise_args.find i
    let (uname, ppname, _) ← arg.match_local_const
    pure (uname, ppname)
  let local_index_instantiations := (index_occs.map get_major_premise_arg_local_names).allSome
  /-
    Right now, this rule only triggers if the major premise arg is exactly a
    local const. We could consider a more permissive rule where the major premise
    arg can be an arbitrary term as long as that term *contains* only a single local
    const.
    -/
    pure <|
    match local_index_instantiations with
    | none => []
    | some [] => []
    | some ((uname, ppname) :: is) => if is.all fun ⟨uname', _⟩ => uname' = uname then [ppname] else []

/-- Naming rule for constructor arguments which are named in the constructor
declaration.
-/
unsafe def constructor_argument_naming_rule_named : constructor_argument_naming_rule := fun i =>
  let arg_name := i.ainfo.aname
  let arg_dep := i.ainfo.dependent
  pure <| if !arg_dep && arg_name.is_likely_generated_binder_name then [] else [arg_name]

/-- Naming rule for constructor arguments whose type is associated with a list of
typical variable names. See `tactic.typical_variable_names`.
-/
unsafe def constructor_argument_naming_rule_type : constructor_argument_naming_rule := fun i =>
  typical_variable_names i.ainfo.type <|> pure []

/-- Naming rule for constructor arguments whose type is in `Prop`.
-/
unsafe def constructor_argument_naming_rule_prop : constructor_argument_naming_rule := fun i => do
  let sort level.zero ← infer_type i.ainfo.type | pure []
  pure [`h]

/-- Fallback constructor argument naming rule. This rule never fails.
-/
unsafe def constructor_argument_naming_rule_fallback : constructor_argument_naming_rule := fun _ => pure [`x]

/-- `apply_constructor_argument_naming_rules info rules` applies the constructor
argument naming rules in `rules` to the constructor argument given by `info`.
Returns the result of the first applicable rule. Fails if no rule is applicable.
-/
unsafe def apply_constructor_argument_naming_rules (info : constructor_argument_naming_info)
    (rules : List constructor_argument_naming_rule) : tactic (List Name) := do
  let names ←
    try_core <|
        rules.mfirst fun r => do
          let names ← r info
          match names with
            | [] => failed
            | _ => pure names
  match names with
    | none => fail "apply_constructor_argument_naming_rules: no applicable naming rule"
    | some names => pure names

/-- Get possible names for a constructor argument. This tactic applies all the
previously defined rules in order. It cannot fail and always returns a nonempty
list.
-/
unsafe def constructor_argument_names (info : constructor_argument_naming_info) : tactic (List Name) :=
  apply_constructor_argument_naming_rules info
    [constructor_argument_naming_rule_rec, constructor_argument_naming_rule_index,
      constructor_argument_naming_rule_named, constructor_argument_naming_rule_type,
      constructor_argument_naming_rule_prop, constructor_argument_naming_rule_fallback]

/-- `intron_fresh n` introduces `n` hypotheses with names generated by
`tactic.mk_fresh_name`.
-/
unsafe def intron_fresh (n : ℕ) : tactic (List expr) :=
  iterate_exactly n (mk_fresh_name >>= intro)

/-- Introduce the new hypotheses generated by the minor premise for a given
constructor. The new hypotheses are given fresh (unique, non-human-friendly)
names. They are later renamed by `constructor_renames`. We delay the generation
of the human-friendly names because when `constructor_renames` is called, more
names may have become unused.

Input:

- `generate_induction_hyps`: whether we generate induction hypotheses (i.e.
  whether `eliminate_hyp` is in `induction` or `cases` mode).
- `cinfo`: information about the constructor.

Output:

- For each constructor argument: (1) the pretty name of the newly introduced
  hypothesis corresponding to the argument; (2) the argument's
  `constructor_argument_info`.
- For each newly introduced induction hypothesis: (1) its pretty name; (2) the
  pretty name of the hypothesis corresponding to the constructor argument from
  which this induction hypothesis was derived; (3) that constructor argument's
  `constructor_argument_info`.
-/
unsafe def constructor_intros (generate_induction_hyps : Bool) (cinfo : constructor_info) :
    tactic (List (Name × constructor_argument_info) × List (Name × Name × constructor_argument_info)) := do
  let args := cinfo.non_param_args
  let arg_hyps ← intron_fresh cinfo.num_non_param_args
  let args := (arg_hyps.map expr.local_pp_name).zip args
  let tt ← pure generate_induction_hyps | pure (args, [])
  let rec_args := args.filter fun x => x.2.is_recursive
  let ih_hyps ← intron_fresh cinfo.num_rec_args
  let ihs := (ih_hyps.map expr.local_pp_name).zip rec_args
  pure (args, ihs)

/-- `ih_name arg_name` is the name `ih_<arg_name>`.
-/
unsafe def ih_name (arg_name : Name) : Name :=
  mkSimpleName ("ih_" ++ arg_name.toString)

/-- Representation of a pattern in the `with n ...` syntax supported by
`induction'` and `cases'`. A `with_pattern` can be:

- `with_pattern.auto` (`with _` or no `with` clause): use the name generated by the tactic.
- `with_pattern.clear` (`with -`): clear this hypothesis and any hypotheses depending on it.
- `with_pattern.exact n` (`with n`): use the name `n` for this hypothesis.
-/
unsafe inductive with_pattern
  | auto
  | clear
  | exact (n : Name)
  deriving has_reflect

namespace WithPattern

open Lean (parser)

open Lean.Parser

/-- Parser for a `with_pattern`. -/
protected unsafe def parser : lean.parser with_pattern :=
  tk "-" *> pure with_pattern.clear <|> tk "_" *> pure with_pattern.auto <|> with_pattern.exact <$> ident

/-- Parser for a `with` clause. -/
unsafe def clause_parser : lean.parser (List with_pattern) :=
  tk "with" *> many with_pattern.parser <|> pure []

/-- `to_name_spec auto_candidates p` returns a description of how the hypothesis to
which the `with_pattern` `p` applies should be named. If this function returns
`none`, the hypothesis should be cleared. If it returns `some (inl n)`, it
should receive exactly the name `n`, even if this shadows other hypotheses. If
it returns `some (inr ns)`, it should receive the first unused name from `ns`.

If `p = auto`, the `auto_candidates` tactic is run to determine candidate names
for the hypothesis (from which the first fresh one is later chosen).
`auto_candidates` must return a nonempty list.
-/
unsafe def to_name_spec (auto_candidates : tactic (List Name)) : with_pattern → tactic (Option (Sum Name (List Name)))
  | auto => (some ∘ Sum.inr) <$> auto_candidates
  | clear => pure none
  | exact n => pure <| some <| Sum.inl n

end WithPattern

/-- If `h` refers to a hypothesis, `clear_dependent_if_exists h` clears `h` and any
hypotheses which depend on it. Otherwise, the tactic does nothing.
-/
unsafe def clear_dependent_if_exists (h : Name) : tactic Unit := do
  let some h ← try_core <| get_local h | pure ()
  clear' tt [h]

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Rename the new hypotheses in the goal for a minor premise.

Input:

- `generate_induction_hyps`: whether we generate induction hypotheses (i.e.
  whether `eliminate_hyp` is in `induction` or `cases` mode).
- `mpinfo`: information about the major premise.
- `iinfo`: information about the inductive type.
- `cinfo`: information about the constructor whose minor premise we are
  processing.
- `with_patterns`: a list of `with` patterns given by the user. These are used
  to name constructor arguments and induction hypotheses. If the list does not
  contain enough patterns for all introduced hypotheses, the remaining ones are
  treated as if the user had given `with_pattern.auto` (`_`).
- `args` and `ihs`: the output of `constructor_intros`.

Output:

- The newly introduced hypotheses corresponding to constructor arguments.
- The newly introduced induction hypotheses.
-/
unsafe def constructor_renames (generate_induction_hyps : Bool) (mpinfo : major_premise_info) (iinfo : inductive_info)
    (cinfo : constructor_info) (with_patterns : List with_pattern) (args : List (Name × constructor_argument_info))
    (ihs : List (Name × Name × constructor_argument_info)) : tactic (List expr × List expr) := do
  let-- Rename constructor arguments
  arg_pp_name_set := name_set.of_list <| args.map Prod.fst
  let iname := iinfo.iname
  let ⟨args, with_patterns⟩ := args.map₂Left' (fun arg p => (arg, p.getOrElse with_pattern.auto)) with_patterns
  let arg_renames ←
    args.mmapFilter fun ⟨⟨old_ppname, ainfo⟩, with_pat⟩ => do
        let some new ← with_pat.to_name_spec (constructor_argument_names ⟨mpinfo, iinfo, cinfo, ainfo⟩) |
          clear_dependent_if_exists old_ppname >> pure none
        let-- Some of the arg hyps may have been cleared by earlier simplification
            -- steps, so get_local may fail.
            some
            old
          ← try_core <| get_local old_ppname | pure none
        pure <| some (old, new)
  let arg_renames := rb_map.of_list arg_renames
  let arg_hyp_map ← rename_fresh arg_renames mk_name_set
  let new_arg_hyps :=
    arg_hyp_map.filterMap fun ⟨old, new⟩ => if arg_pp_name_set.contains old.local_pp_name then some new else none
  let arg_hyp_map : name_map expr := rb_map.of_list <| arg_hyp_map.map fun ⟨old, new⟩ => (old.local_pp_name, new)
  let-- Rename induction hypotheses (if we generated them)
    tt
    ← pure generate_induction_hyps | pure (new_arg_hyps, [])
  let ih_pp_name_set := name_set.of_list <| ihs.map Prod.fst
  let ihs := ihs.map₂Left (fun ih p => (ih, p.getOrElse with_pattern.auto)) with_patterns
  let single_ih := ihs.length = 1
  let ih_renames ←
    ihs.mmapFilter fun ⟨⟨ih_hyp_ppname, arg_hyp_ppname, _⟩, with_pat⟩ => do
        let some arg_hyp ← pure <| arg_hyp_map.find arg_hyp_ppname |
          "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
        let some new ←
          with_pat.to_name_spec
              (pure <|
                if single_ih then [`ih, ih_name arg_hyp.local_pp_name]
                else-- If we have only a single IH which hasn't been named explicitly in a
                  -- `with` clause, the preferred name is "ih". If that is taken, we fall
                  -- back to the name the IH would ordinarily receive.
                  [ih_name arg_hyp.local_pp_name]) |
          clear_dependent_if_exists ih_hyp_ppname >> pure none
        let some ih_hyp ← try_core <| get_local ih_hyp_ppname | pure none
        pure <| some (ih_hyp, new)
  let ih_hyp_map ← rename_fresh (rb_map.of_list ih_renames) mk_name_set
  let new_ih_hyps :=
    ih_hyp_map.filterMap fun ⟨old, new⟩ => if ih_pp_name_set.contains old.local_pp_name then some new else none
  pure (new_arg_hyps, new_ih_hyps)

/-!
## Generalisation

`induction'` can generalise the goal before performing an induction, which gives
us a more general induction hypothesis. We call this 'auto-generalisation'.
-/


/-- A value of `generalization_mode` describes the behaviour of the
auto-generalisation functionality:

- `generalize_all_except hs` means that the `hs` remain fixed and all other
  hypotheses are generalised. However, there are three exceptions:

  * Hypotheses depending on any `h` in `hs` also remain fixed. If we were to
    generalise them, we would have to generalise `h` as well.
  * Hypotheses which do not occur in the target and which do not mention the
    major premise or its dependencies are never generalised. Generalising them
    would not lead to a more general induction hypothesis.
  * Local definitions (hypotheses of the form `h : T := t`) and their
    dependencies are not generalised. This is due to limitations of the
    implementation; local definitions could in principle be generalised.

- `generalize_only hs` means that only the `hs` are generalised. Exception:
  hypotheses which depend on the major premise are generalised even if they do
  not appear in `hs`.
-/
inductive GeneralizationMode
  | generalize_all_except (hs : List Name) : generalization_mode
  | generalize_only (hs : List Name) : generalization_mode
  deriving has_reflect

instance : Inhabited GeneralizationMode :=
  ⟨GeneralizationMode.generalize_all_except []⟩

namespace GeneralizationMode

/-- Given the major premise and a generalization_mode, this function returns the
unique names of the hypotheses that should be generalized. See
`generalization_mode` for what these are.
-/
unsafe def to_generalize (major_premise : expr) : GeneralizationMode → tactic name_set
  | generalize_only ns => do
    let major_premise_rev_deps ← reverse_dependencies_of_hyps [major_premise]
    let major_premise_rev_deps := name_set.of_list <| major_premise_rev_deps.map local_uniq_name
    let ns ← ns.mmap (Functor.map local_uniq_name ∘ get_local)
    pure <| major_premise_rev_deps ns
  | generalize_all_except fixed => do
    let fixed ← fixed.mmap get_local
    let tgt ← target
    let tgt_dependencies := tgt.list_local_const_unique_names
    let major_premise_type ← infer_type major_premise
    let major_premise_dependencies ← dependency_name_set_of_hyp_inclusive major_premise
    let defs ← local_defs
    let fixed_dependencies ← (major_premise :: defs ++ fixed).mmap dependency_name_set_of_hyp_inclusive
    let fixed_dependencies := fixed_dependencies.foldl name_set.union mk_name_set
    let ctx ← local_context
    let to_revert ←
      ctx.mmapFilter fun h => do
          let h_depends_on_major_premise_deps
            ←-- TODO `hyp_depends_on_local_name_set` is somewhat expensive
                hyp_depends_on_local_name_set
                h major_premise_dependencies
          let h_name := h.local_uniq_name
          let rev :=
            ¬fixed_dependencies.contains h_name ∧ (h_depends_on_major_premise_deps ∨ tgt_dependencies.contains h_name)
          /-
                  I think `h_depends_on_major_premise_deps` is an overapproximation. What we
                  actually want is any hyp that depends either on the major_premise or on one
                  of the major_premise's index args. (But the overapproximation seems to work
                  okay in practice as well.)
                  -/
              pure <|
              if rev then some h_name else none
    pure <| name_set.of_list to_revert

end GeneralizationMode

/-- Generalize hypotheses for the given major premise and generalization mode. See
`generalization_mode` and `to_generalize`.
-/
unsafe def generalize_hyps (major_premise : expr) (gm : GeneralizationMode) : tactic ℕ := do
  let to_revert ← gm.to_generalize major_premise
  let ⟨n, _⟩ ← unfreezing (revert_name_set to_revert)
  pure n

/-!
## Complex Index Generalisation

A *complex* expression is any expression that is not merely a local constant.
When such a complex expression appears as an argument of the major premise, and
when that argument is an index of the inductive type, we must generalise the
complex expression. E.g. when we operate on the major premise `fin (2 + n)`
(assuming that `fin` is encoded as an inductive type), the `2 + n` is a complex
index argument. To generalise it, we replace it with a new hypothesis
`index : ℕ` and add an equation `induction_eq : index = 2 + n`.
-/


/-- Generalise the complex index arguments.

Input:

- `major premise`: the major premise.
- `num_params`: the number of parameters of the inductive type.
- `generate_induction_hyps`: whether we generate induction hypotheses (i.e.
  whether `eliminate_hyp` is in `induction` or `cases` mode).

Output:

- The new major premise. This procedure may change the major premise's type
  signature, so the old major premise hypothesis is invalidated.
- The number of index placeholder hypotheses we introduced.
- The index placeholder hypotheses we introduced.
- The number of hypotheses which were reverted because they contain complex
  indices.
-/
/-
TODO The following function currently replaces complex index arguments
everywhere in the goal, not only in the major premise. Such replacements are
sometimes necessary to make sure that the goal remains type-correct. However,
the replacements can also have the opposite effect, yielding unprovable
subgoals. The test suite contains one such case. There is probably a middle
ground between 'replace everywhere' and 'replace only in the major premise', but
I don't know what exactly this middle ground is. See also the discussion at
https://github.com/leanprover-community/mathlib/pull/5027#discussion_r538902424
-/
unsafe def generalize_complex_index_args (major_premise : expr) (num_params : ℕ) (generate_induction_hyps : Bool) :
    tactic (expr × ℕ × List Name × ℕ) :=
  focus1 <| do
    let major_premise_type ← infer_type major_premise
    let (major_premise_head, major_premise_args) ← get_app_fn_args_whnf major_premise_type
    let ⟨major_premise_param_args, major_premise_index_args⟩ := major_premise_args.splitAt num_params
    let-- TODO Add equations only for complex index args (not all index args).
    -- This shouldn't matter semantically, but we'd get simpler terms.
    js := major_premise_index_args
    let ctx ← local_context
    let tgt ← target
    let major_premise_deps ← dependency_name_set_of_hyp_inclusive major_premise
    let relevant_ctx
      ←-- Revert the hypotheses which depend on the index args or the major_premise.
            -- We exclude dependencies of the major premise because we can't replace their
            -- index occurrences anyway when we apply the recursor.
            ctx.mfilter
          fun h => do
          let dep_of_major_premise := major_premise_deps.contains h.local_uniq_name
          let dep_on_major_premise ← hyp_depends_on_locals h [major_premise]
          let H ← infer_type h
          let dep_of_index ← js.many fun j => kdepends_on H j
          -- TODO We need a variant of `kdepends_on` that takes local defs into account.
              pure <|
              dep_on_major_premise ∧ h ≠ major_premise ∨ dep_of_index ∧ ¬dep_of_major_premise
    let ⟨relevant_ctx_size, relevant_ctx⟩ ←
      unfreezing <| do
          let r ← revert_lst' relevant_ctx
          revert major_premise
          pure r
    let-- Create the local constants that will replace the index args. We have to be
    -- careful to get the right types.
    go : expr → List expr → tactic (List expr) := fun j ks => do
      let J ← infer_type j
      let k ← mk_local' `index BinderInfo.default J
      let ks ← ks.mmap fun k' => kreplace k' j k
      pure <| k :: ks
    let ks ← js.mfoldr go []
    let js_ks := js.zip ks
    let new_ctx
      ←-- Replace the index args in the relevant context.
            relevant_ctx.mmap
          fun h => js_ks.mfoldr (fun ⟨j, k⟩ h => kreplace h j k) h
    let-- Replace the index args in the major premise.
    new_major_premise_type := major_premise_head.mk_app (major_premise_param_args ++ ks)
    let new_major_premise :=
      local_const major_premise.local_uniq_name major_premise.local_pp_name major_premise.binding_info
        new_major_premise_type
    let new_tgt
      ←-- Replace the index args in the target.
            js_ks.mfoldr
          (fun ⟨j, k⟩ tgt => kreplace tgt j k) tgt
    let new_tgt := new_tgt.pis (new_major_premise :: new_ctx)
    let-- Generate the index equations and their proofs.
    eq_name := if generate_induction_hyps then `induction_eq else `cases_eq
    let step2_input := js_ks.map fun ⟨j, k⟩ => (eq_name, j, k)
    let eqs_and_proofs ← generalizes.step2 reducible step2_input
    let eqs := eqs_and_proofs.map Prod.fst
    let eq_proofs := eqs_and_proofs.map Prod.snd
    -- Assert the generalized goal and derive the current goal from it.
        generalizes.step3
        new_tgt js ks eqs eq_proofs
    let-- Introduce the index variables and major premise. The index equations
    -- and the relevant context remain reverted.
    num_index_vars := js.length
    let index_vars ← intron' num_index_vars
    let index_equations ← intron' num_index_vars
    let major_premise ← intro1
    revert_lst index_equations
    let index_vars := index_vars.map local_pp_name
    pure (major_premise, index_vars, index_vars, relevant_ctx_size)

/-!
## Simplification of Induction Hypotheses

Auto-generalisation and complex index generalisation may produce unnecessarily
complex induction hypotheses. We define a simplification algorithm that recovers
understandable induction hypotheses in many practical cases.
-/


-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Process one index equation for `simplify_ih`.

Input: a local constant `h : x = y` or `h : x == y`.

Output: A proof of `x = y` or `x == y` and possibly a local constant of type
`x = y` or `x == y` used in the proof. More specifically:

- For `h : x = y` and `x` defeq `y`, we return the proof of `x = y` by
  reflexivity and `none`.
- For `h : x = y` and `x` not defeq `y`, we return `h` and `h`.
- For `h : x == y` where `x` and `y` have defeq types:
  - If `x` defeq `y`, we return the proof of `x == y` by reflexivity and `none`.
  - If `x` not defeq `y`, we return `heq_of_eq h'` and a fresh local constant
    `h' : x = y`.
- For `h : x == y` where `x` and `y` do not have defeq types, we return
  `h` and `h`.

Checking for definitional equality of the left- and right-hand sides may assign
metavariables.
-/
unsafe def process_index_equation : expr → tactic (expr × Option expr)
  | h@(local_const _ ppname binfo T@(app (app (app (const `eq [u]) type) lhs) rhs)) => do
    let rhs_eq_lhs ← succeeds <| unify rhs lhs
    -- Note: It is important that we `unify rhs lhs` rather than `unify lhs rhs`.
        -- This is because `lhs` and `rhs` may be metavariables which represent
        -- Π-bound variables, so if they unify, we want to assign `rhs := lhs`.
        -- If we assign `lhs := rhs` instead, it can happen that `lhs` is used before
        -- `rhs` is bound, so the generated term becomes ill-typed.
        if rhs_eq_lhs then pure ((const `eq.refl [u]) type lhs, none)
      else do
        pure (h, some h)
  | h@(local_const uname ppname binfo T@(app (app (app (app (const `heq [u]) lhs_type) lhs) rhs_type) rhs)) => do
    let lhs_type_eq_rhs_type ← succeeds <| is_def_eq lhs_type rhs_type
    if ¬lhs_type_eq_rhs_type then do
        pure (h, some h)
      else do
        let lhs_eq_rhs ← succeeds <| unify rhs lhs
        -- See note above about `unify rhs lhs`.
            if lhs_eq_rhs then pure ((const `heq.refl [u]) lhs_type lhs, none)
          else do
            let c ← mk_local' ppname binfo <| (const `eq [u]) lhs_type lhs rhs
            let arg := (const `heq_of_eq [u]) lhs_type lhs rhs c
            pure (arg, some c)
  | local_const _ _ _ T =>
    "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
  | e =>
    "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"

/-- `assign_local_to_unassigned_mvar mv pp_name binfo`, where `mv` is a
metavariable, acts as follows:

- If `mv` is assigned, it is not changed and the tactic returns `none`.
- If `mv` is not assigned, it is assigned a fresh local constant with
  the type of `mv`, pretty name `pp_name` and binder info `binfo`. This local
  constant is returned.
-/
unsafe def assign_local_to_unassigned_mvar (mv : expr) (pp_name : Name) (binfo : BinderInfo) : tactic (Option expr) :=
  do
  let ff ← is_assigned mv | pure none
  let type ← infer_type mv
  let c ← mk_local' pp_name binfo type
  unify mv c
  pure c

/-- Apply `assign_local_to_unassigned_mvar` to a list of metavariables. Returns the
newly created local constants.
-/
unsafe def assign_locals_to_unassigned_mvars (mvars : List (expr × Name × BinderInfo)) : tactic (List expr) :=
  mvars.mmapFilter fun ⟨mv, pp_name, binfo⟩ => assign_local_to_unassigned_mvar mv pp_name binfo

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Simplify an induction hypothesis.

Input: a local constant
```
ih : ∀ (a₁ : A₁) ... (aₙ : Aₙ) (b₁ : B₁) ... (bₘ : Bₘ)
       (eq₁ : y₁ = z₁) ... (eqₖ : yₒ = zₒ), P
```
where `n = num_leading_pis`, `m = num_generalized` and `o = num_index_vars`.
The `aᵢ` are arguments of the type of the constructor argument to which this
induction hypothesis belongs (usually zero). The `xᵢ` are hypotheses that we
generalised over before performing induction. The `eqᵢ` are index equations.

Output: a new local constant
```
ih' : ∀ (a'₁ : A'₁) ... (b'ₖ : B'ₖ) (eq'₁ : y'₁ = z'₁) ... (eq'ₗ : y'ₗ = z'ₗ), P'
```
This new induction hypothesis is derived from `ih` by removing those `eqᵢ` whose
left- and right-hand sides can be unified. This unification may also determine
some of the `aᵢ` and `bᵢ`. The `a'ᵢ`, `b'ᵢ` and `eq'ᵢ` are those `aᵢ`, `bᵢ` and
`eqᵢ` that were not removed by this process.

Some of the `eqᵢ` may be heterogeneous: `eqᵢ : yᵢ == zᵢ`. In this case, we
proceed as follows:

- If `yᵢ` and `zᵢ` are defeq, then `eqᵢ` is removed.
- If `yᵢ` and `zᵢ` are not defeq but their types are, then `eqᵢ` is replaced by
  `eq'ᵢ : x = y`.
- Otherwise `eqᵢ` remains unchanged.
-/
/-
TODO `simplify_ih` currently uses Lean's builtin unification procedure to
process the index equations. This procedure has some limitations. For example,
we would like to clear an IH that assumes `0 = 1` since this IH can never be
applied, but Lean's unification doesn't allow us to conclude this.

It would therefore be preferable to use the algorithm from
`tactic.unify_equations` instead. There is no problem with this in principle,
but it requires a complete refactoring of `unify_equations` so that it works
not only on hypotheses but on arbitrary terms.
-/
unsafe def simplify_ih (num_leading_pis : ℕ) (num_generalized : ℕ) (num_index_vars : ℕ) (ih : expr) : tactic expr := do
  let T ← infer_type ih
  let-- Replace the `xᵢ` with fresh metavariables.
    (generalized_arg_mvars, body)
    ← open_n_pis_metas' T (num_leading_pis + num_generalized)
  let-- Replace the `eqᵢ` with fresh local constants.
    (index_eq_lcs, body)
    ← open_n_pis body num_index_vars
  let new_index_eq_lcs_new_args
    ←-- Process the `eqᵢ` local constants, yielding
          -- - `new_args`: proofs of `yᵢ = zᵢ`.
          -- - `new_index_eq_lcs`: local constants of type `yᵢ = zᵢ` or `yᵢ == zᵢ` used
          --   in `new_args`.
          index_eq_lcs.mmap
        process_index_equation
  let (new_args, new_index_eq_lcs) := new_index_eq_lcs_new_args.unzip
  let new_index_eq_lcs := new_index_eq_lcs.reduceOption
  let new_generalized_arg_lcs
    ←-- Assign fresh local constants to those `xᵢ` metavariables that were not
        -- assigned by the previous step.
        assign_locals_to_unassigned_mvars
        generalized_arg_mvars
  let new_generalized_arg_lcs
    ←-- Instantiate the metavariables assigned in the previous steps.
          new_generalized_arg_lcs.mmap
        instantiate_mvars
  let new_index_eq_lcs ← new_index_eq_lcs.mmap instantiate_mvars
  let b
    ←-- Construct a proof of the new induction hypothesis by applying `ih` to the
        -- `xᵢ` metavariables and the `new_args`, then abstracting over the
        -- `new_index_eq_lcs` and the `new_generalized_arg_lcs`.
        instantiate_mvars <|
        ih.mk_app (generalized_arg_mvars.map Prod.fst ++ new_args)
  let new_ih ← lambdas (new_generalized_arg_lcs ++ new_index_eq_lcs) b
  -- Type-check the new induction hypothesis as a sanity check.
        type_check
        new_ih <|>
      "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
  let ih'
    ←-- Replace the old induction hypothesis with the new one.
        note
        ih.local_pp_name none new_ih
  clear ih
  pure ih'

/-!
## Temporary utilities

The utility functions in this section should be removed pending certain changes
to Lean's standard library.
-/


/-- Updates the tags of new subgoals produced by `cases` or `induction`. `in_tag`
  is the initial tag, i.e. the tag of the goal on which `cases`/`induction` was
  applied. `rs` should contain, for each subgoal, the constructor name
  associated with that goal and the hypotheses that were introduced.
-/
-- TODO Copied from init.meta.interactive. Make that function non-private.
unsafe def set_cases_tags (in_tag : Tag) (rs : List (Name × List expr)) : tactic Unit := do
  let gs ← get_goals
  match gs with
    |-- if only one goal was produced, we should not make the tag longer
      [g] =>
      set_tag g in_tag
    | _ =>
      let tgs : List (Name × List expr × expr) := rs (fun ⟨n, new_hyps⟩ g => ⟨n, new_hyps, g⟩) gs
      tgs fun ⟨n, new_hyps, g⟩ =>
        with_enable_tags <| set_tag g <| (case_tag.from_tag_hyps (n :: in_tag) (new_hyps expr.local_uniq_name)).render

end Eliminate

/-!
## The Elimination Tactics

Finally, we define the tactics `induction'` and `cases'` tactics as well as the
non-interactive variant `eliminate_hyp.`
-/


open Eliminate

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- `eliminate_hyp generate_ihs h gm with_patterns` performs induction or case
analysis on the hypothesis `h`. If `generate_ihs` is true, the tactic performs
induction, otherwise case analysis.

In case analysis mode, `eliminate_hyp` is very similar to `tactic.cases`. The
only differences (assuming no bugs in `eliminate_hyp`) are that `eliminate_hyp`
can do case analysis on a slightly larger class of hypotheses and that it
generates more human-friendly names.

In induction mode, `eliminate_hyp` is similar to `tactic.induction`, but with
more significant differences:

- If `h` (the hypothesis we are performing induction on) has complex indices,
  `eliminate_hyp` 'remembers' them. A complex expression is any expression that
  is not merely a local hypothesis. A hypothesis `h : I p₁ ... pₙ j₁ ... jₘ`,
  where `I` is an inductive type with `n` parameters and `m` indices, has a
  complex index if any of the `jᵢ` are complex. In this situation, standard
  `induction` effectively forgets the exact values of the complex indices,
  which often leads to unprovable goals. `eliminate_hyp` 'remembers' them by
  adding propositional equalities. As a result, you may find equalities named
  `induction_eq` in your goal, and the induction hypotheses may also quantify
  over additional equalities.
- `eliminate_hyp` generalises induction hypotheses as much as possible by
  default. This means that if you eliminate `n` in the goal
  ```
  n m : ℕ
  ⊢ P n m
  ```
  the induction hypothesis is `∀ m, P n m` instead of `P n m`.

  You can modify this behaviour by giving a different generalisation mode `gm`;
  see `tactic.eliminate.generalization_mode`.
- `eliminate_hyp` generates much more human-friendly names than `induction`. It
  also clears more redundant hypotheses.
- `eliminate_hyp` currently does not support custom induction principles a la
  `induction using`.

The `with_patterns` can be used to give names for the hypotheses introduced by
`eliminate_hyp`. See `tactic.eliminate.with_pattern` for details.

To debug this tactic, use

```
set_option trace.eliminate_hyp true
```
-/
unsafe def eliminate_hyp (generate_ihs : Bool) (major_premise : expr)
    (gm := GeneralizationMode.generalize_all_except []) (with_patterns : List with_pattern := []) : tactic Unit :=
  focus1 <| do
    let mpinfo ← get_major_premise_info major_premise
    let major_premise_type := mpinfo.type
    let major_premise_args := mpinfo.args.values.reverse
    let env ← get_env
    let iname
      ←-- Get info about the inductive type
            get_app_fn_const_whnf
            major_premise_type <|>
          "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
    let iinfo ← get_inductive_info iname
    -- We would like to disallow mutual/nested inductive types, since these have
        -- complicated recursors which we probably don't support. However, there seems
        -- to be no way to find out whether an inductive type is mutual/nested.
        -- (`environment.is_ginductive` doesn't seem to work.)
        trace_state_eliminate_hyp
        "State before complex index generalisation:"
    let-- Generalise complex indices
      (major_premise, num_index_vars, index_var_names, num_index_generalized)
      ← generalize_complex_index_args major_premise iinfo.num_params generate_ihs
    trace_state_eliminate_hyp "State after complex index generalisation and before auto-generalisation:"
    let num_auto_generalized
      ←-- Generalise hypotheses according to the given generalization_mode.
          generalize_hyps
          major_premise gm
    let num_generalized := num_index_generalized + num_auto_generalized
    let in_tag
      ←-- NOTE: The previous step may have changed the unique names of all hyps in
        -- the context.
        -- Record the current case tag.
        get_main_tag
    trace_state_eliminate_hyp "State after auto-generalisation and before recursor application:"
    let-- Apply the recursor. We first try the nondependent recursor, then the
    -- dependent recursor (if available).
    -- Construct a pexpr `@rec _ ... _ major_premise`. Why not
    -- ```(%%rec %%major_premise)?` Because for whatever reason, `false.rec_on`
    -- takes the motive not as an implicit argument, like any other recursor, but
    -- as an explicit one. Why not something based on `mk_app` or `mk_mapp`?
    -- Because we need the special elaborator support for `elab_as_eliminator`
    -- definitions.
    rec_app : Name → pexpr := fun rec_suffix =>
      (unchecked_cast expr.mk_app : pexpr → List pexpr → pexpr) (pexpr.mk_explicit (const (iname ++ rec_suffix) []))
        (List.repeat pexpr.mk_placeholder (major_premise_args.length + 1) ++ [to_pexpr major_premise])
    let rec_suffix := if generate_ihs then "rec_on" else "cases_on"
    let drec_suffix := if generate_ihs then "drec_on" else "dcases_on"
    interactive.apply (rec_app rec_suffix) <|>
        interactive.apply (rec_app drec_suffix) <|>
          "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
    let-- Prepare the "with" names for each constructor case.
    with_patterns :=
      Prod.fst <| with_patterns.takeList (iinfo.constructors.map constructor_info.num_nameable_hypotheses)
    let constrs := iinfo.constructors.zip with_patterns
    let
      cases :-- For each case (constructor):
        List
        (Option (Name × List expr))
      ←
      focus <|
          constrs.map fun ⟨cinfo, with_patterns⟩ => do
            trace_eliminate_hyp "============"
            trace_eliminate_hyp <| f! "Case {cinfo}"
            trace_state_eliminate_hyp "Initial state:"
            let major_premise_type
              ←-- Get the major premise's arguments. (Some of these may have changed due
                  -- to the generalising step above.)
                  infer_type
                  major_premise
            let major_premise_args ← get_app_args_whnf major_premise_type
            -- Clear the eliminated hypothesis (if possible)
                try <|
                clear major_premise
            -- Clear the index args (unless other stuff in the goal depends on them)
                major_premise_args
                (try ∘ clear)
            trace_state_eliminate_hyp
                "State after clearing the major premise (and its arguments) and before introductions:"
            let-- Introduce the constructor arguments
              (constructor_args, ihs)
              ← constructor_intros generate_ihs cinfo
            -- Introduce the auto-generalised hypotheses.
                intron
                num_auto_generalized
            let index_equations
              ←-- Introduce the index equations
                  intron'
                  num_index_vars
            let index_equations := index_equations.map local_pp_name
            -- Introduce the hypotheses that were generalised during index
                -- generalisation.
                intron
                num_index_generalized
            trace_state_eliminate_hyp "State after introductions and before simplifying index equations:"
            let-- Simplify the index equations. Stop after this step if the goal has been
              -- solved by the simplification.
              ff
              ← unify_equations index_equations |
              trace_eliminate_hyp "Case solved while simplifying index equations." >> pure none
            trace_state_eliminate_hyp "State after simplifying index equations and before simplifying IHs:"
            -- Simplify the induction hypotheses
                -- NOTE: The previous step may have changed the unique names of the
                -- induction hypotheses, so we have to locate them again. Their pretty
                -- names should be unique in the context, so we can use these.
                ihs
                fun ⟨ih, _, arg_info⟩ => do
                let ih ← get_local ih
                let some num_leading_pis ← pure arg_info |
                  "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
                simplify_ih num_leading_pis num_auto_generalized num_index_vars ih
            trace_state_eliminate_hyp "State after simplifying IHs and before clearing index variables:"
            -- Try to clear the index variables. These often become unused during
                -- the index equation simplification step.
                index_var_names
                fun h => try (get_local h >>= clear)
            trace_state_eliminate_hyp "State after clearing index variables and before renaming:"
            let-- Rename the constructor names and IHs. We do this here (rather than
              -- earlier, when we introduced them) because there may now be less
              -- hypotheses in the context, and therefore more of the desired
              -- names may be free.
              (constructor_arg_hyps, ih_hyps)
              ← constructor_renames generate_ihs mpinfo iinfo cinfo with_patterns constructor_args ihs
            trace_state_eliminate_hyp "Final state:"
            -- Return the constructor name and the renamable new hypotheses. These are
                -- the hypotheses that can later be renamed by the `case` tactic. Note
                -- that index variables and index equations are not renamable. This may be
                -- counterintuitive in some cases, but it's surprisingly difficult to
                -- catch exactly the relevant hyps here.
                pure <|
                some (cinfo, constructor_arg_hyps ++ ih_hyps)
    set_cases_tags in_tag cases
    pure ()

/-- A variant of `tactic.eliminate_hyp` which performs induction or case analysis on
an arbitrary expression. `eliminate_hyp` requires that the major premise is a
hypothesis. `eliminate_expr` lifts this restriction by generalising the goal
over the major premise before calling `eliminate_hyp`. The generalisation
replaces the major premise with a new hypothesis `x` everywhere in the goal.
If `eq_name` is `some h`, an equation `h : major_premise = x` is added to
remember the value of the major premise.
-/
unsafe def eliminate_expr (generate_induction_hyps : Bool) (major_premise : expr) (eq_name : Option Name := none)
    (gm := GeneralizationMode.generalize_all_except []) (with_patterns : List with_pattern := []) : tactic Unit := do
  let major_premise_revdeps ← reverse_dependencies_of_hyps [major_premise]
  let num_reverted ← unfreezing (revert_lst major_premise_revdeps)
  let hyp ←
    match eq_name with
      | some h => do
        let x ← get_unused_name `x
        interactive.generalize h () (to_pexpr major_premise, x)
        get_local x
      | none => do
        if major_premise then pure major_premise
          else do
            let x ← get_unused_name `x
            generalize' major_premise x
  intron num_reverted
  eliminate_hyp generate_induction_hyps hyp gm with_patterns

end Tactic

namespace Tactic.Interactive

open Tactic Tactic.Eliminate Interactive Interactive.Types Lean.Parser

/-- Parse a `fixing` or `generalizing` clause for `induction'` or `cases'`.
-/
unsafe def generalisation_mode_parser : lean.parser GeneralizationMode :=
  tk "fixing" *>
      (tk "*" *> pure (GeneralizationMode.generalize_only []) <|>
        generalization_mode.generalize_all_except <$> many ident) <|>
    tk "generalizing" *> generalization_mode.generalize_only <$> many ident <|>
      pure (GeneralizationMode.generalize_all_except [])

/-- A variant of `tactic.interactive.induction`, with the following differences:

- If the major premise (the hypothesis we are performing induction on) has
  complex indices, `induction'` 'remembers' them. A complex expression is any
  expression that is not merely a local hypothesis. A major premise
  `h : I p₁ ... pₙ j₁ ... jₘ`, where `I` is an inductive type with `n`
  parameters and `m` indices, has a complex index if any of the `jᵢ` are
  complex. In this situation, standard `induction` effectively forgets the exact
  values of the complex indices, which often leads to unprovable goals.
  `induction'` 'remembers' them by adding propositional equalities. As a
  result, you may find equalities named `induction_eq` in your goal, and the
  induction hypotheses may also quantify over additional equalities.
- `induction'` generalises induction hypotheses as much as possible by default.
  This means that if you eliminate `n` in the goal
  ```
  n m : ℕ
  ⊢ P n m
  ```
  the induction hypothesis is `∀ m, P n m` instead of `P n m`.
- `induction'` generates much more human-friendly names than `induction`. It
  also clears redundant hypotheses more aggressively.
- `induction'` currently does not support custom induction principles a la
  `induction using`.

Like `induction`, `induction'` supports some modifiers:

`induction' e with n₁ ... nₘ` uses the names `nᵢ` for the new hypotheses.
Instead of a name, you can also give an underscore (`_`) to have `induction'`
generate a name for you, or a hyphen (`-`) to clear the hypothesis and any
hypotheses that depend on it.

`induction' e fixing h₁ ... hₙ` fixes the hypotheses `hᵢ`, so the induction
hypothesis is not generalised over these hypotheses.

`induction' e fixing *` fixes all hypotheses. This disables the generalisation
functionality, so this mode behaves like standard `induction`.

`induction' e generalizing h₁ ... hₙ` generalises only the hypotheses `hᵢ`. This
mode behaves like `induction e generalizing h₁ ... hₙ`.

`induction' t`, where `t` is an arbitrary term (rather than a hypothesis),
generalises the goal over `t`, then performs induction on the generalised goal.

`induction' h : t = x` is similar, but also adds an equation `h : t = x` to
remember the value of `t`.

To debug this tactic, use

```
set_option trace.eliminate_hyp true
```
-/
unsafe def induction' (major_premise : parse cases_arg_p) (gm : parse generalisation_mode_parser)
    (with_patterns : parse with_pattern.clause_parser) : tactic Unit := do
  let ⟨eq_name, e⟩ := major_premise
  let e ← to_expr e
  eliminate_expr tt e eq_name gm with_patterns

/-- A variant of `tactic.interactive.cases`, with minor changes:

- `cases'` can perform case analysis on some (rare) goals that `cases` does not
  support.
- `cases'` generates much more human-friendly names for the new hypotheses it
  introduces.

This tactic supports the same modifiers as `cases`, e.g.

```
cases' H : e = x with n _ o
```

This is almost exactly the same as `tactic.interactive.induction'`, only that no
induction hypotheses are generated.

To debug this tactic, use

```
set_option trace.eliminate_hyp true
```
-/
unsafe def cases' (major_premise : parse cases_arg_p) (with_patterns : parse with_pattern.clause_parser) :
    tactic Unit := do
  let ⟨eq_name, e⟩ := major_premise
  let e ← to_expr e
  eliminate_expr ff e eq_name (generalization_mode.generalize_only []) with_patterns

end Tactic.Interactive

