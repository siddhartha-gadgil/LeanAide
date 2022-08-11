/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.Tactic.Protected
import Mathbin.Algebra.Group.ToAdditive

/-!
# simps attribute

This file defines the `@[simps]` attribute, to automatically generate `simp` lemmas
reducing a definition when projections are applied to it.

## Implementation Notes

There are three attributes being defined here
* `@[simps]` is the attribute for objects of a structure or instances of a class. It will
  automatically generate simplification lemmas for each projection of the object/instance that
  contains data. See the doc strings for `simps_attr` and `simps_cfg` for more details and
  configuration options.
* `@[_simps_str]` is automatically added to structures that have been used in `@[simps]` at least
  once. This attribute contains the data of the projections used for this structure by all following
  invocations of `@[simps]`.
* `@[notation_class]` should be added to all classes that define notation, like `has_mul` and
  `has_zero`. This specifies that the projections that `@[simps]` used are the projections from
  these notation classes instead of the projections of the superclasses.
  Example: if `has_mul` is tagged with `@[notation_class]` then the projection used for `semigroup`
  will be `λ α hα, @has_mul.mul α (@semigroup.to_has_mul α hα)` instead of `@semigroup.mul`.

## Tags

structures, projections, simp, simplifier, generates declarations
-/


open Tactic Expr Option Sum

setup_tactic_parser

initialize
  registerTraceClass.1 `simps.verbose

initialize
  registerTraceClass.1 `simps.debug

/-- Projection data for a single projection of a structure, consisting of the following fields:
- the name used in the generated `simp` lemmas
- an expression used by simps for the projection. It must be definitionally equal to an original
  projection (or a composition of multiple projections).
  These expressions can contain the universe parameters specified in the first argument of
  `simps_str_attr`.
- a list of natural numbers, which is the projection number(s) that have to be applied to the
  expression. For example the list `[0, 1]` corresponds to applying the first projection of the
  structure, and then the second projection of the resulting structure (this assumes that the
  target of the first projection is a structure with at least two projections).
  The composition of these projections is required to be definitionally equal to the provided
  expression.
- A boolean specifying whether `simp` lemmas are generated for this projection by default.
- A boolean specifying whether this projection is written as prefix.
-/
@[protect_proj]
unsafe structure projection_data where
  Name : Name
  expr : expr
  proj_nrs : List ℕ
  is_default : Bool
  IsPrefix : Bool
  deriving has_reflect, Inhabited

/-- Temporary projection data parsed from `initialize_simps_projections` before the expression
  matching this projection has been found. Only used internally in `simps_get_raw_projections`. -/
unsafe structure parsed_projection_data where
  orig_name : Name
  -- name for this projection used in the structure definition
  new_name : Name
  -- name for this projection used in the generated `simp` lemmas
  is_default : Bool
  IsPrefix : Bool

section

open Format

unsafe instance : has_to_tactic_format projection_data :=
  ⟨fun ⟨a, b, c, d, e⟩ =>
    (fun x =>
        group <|
          nest 1 <|
            to_fmt "⟨" ++ to_fmt a ++ to_fmt "," ++ line ++ x ++ to_fmt "," ++ line ++ to_fmt c ++ to_fmt "," ++ line ++
                      to_fmt d ++
                    to_fmt "," ++
                  line ++
                to_fmt e ++
              to_fmt "⟩") <$>
      pp b⟩

unsafe instance : has_to_format parsed_projection_data :=
  ⟨fun ⟨a, b, c, d⟩ =>
    group <|
      nest 1 <|
        to_fmt "⟨" ++ to_fmt a ++ to_fmt "," ++ line ++ to_fmt b ++ to_fmt "," ++ line ++ to_fmt c ++ to_fmt "," ++
              line ++
            to_fmt d ++
          to_fmt "⟩"⟩

end

/-- The type of rules that specify how metadata for projections in changes.
  See `initialize_simps_projection`. -/
abbrev ProjectionRule :=
  Sum (Name × Name) Name × Bool

/-- The `@[_simps_str]` attribute specifies the preferred projections of the given structure,
used by the `@[simps]` attribute.
- This will usually be tagged by the `@[simps]` tactic.
- You can also generate this with the command `initialize_simps_projections`.
- To change the default value, see Note [custom simps projection].
- You are strongly discouraged to add this attribute manually.
- The first argument is the list of names of the universe variables used in the structure
- The second argument is a list that consists of the projection data for each projection.
-/
@[user_attribute]
unsafe def simps_str_attr : user_attribute Unit (List Name × List projection_data) where
  Name := `_simps_str
  descr := "An attribute specifying the projection of the given structure."
  parser := failed

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- The `@[notation_class]` attribute specifies that this is a notation class,
  and this notation should be used instead of projections by @[simps].
  * The first argument `tt` for notation classes and `ff` for classes applied to the structure,
    like `has_coe_to_sort` and `has_coe_to_fun`
  * The second argument is the name of the projection (by default it is the first projection
    of the structure)
-/
@[user_attribute]
unsafe def notation_class_attr : user_attribute Unit (Bool × Option Name) where
  Name := `notation_class
  descr := "An attribute specifying that this is a notation class. Used by @[simps]."
  parser := Prod.mk <$> Option.isNone <$> «expr ?» (tk "*") <*> «expr ?» ident

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1209:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
attribute
  [«./././Mathport/Syntax/Translate/Basic.lean:1209:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg»]
  Zero One Add Mul Inv Neg Sub Div Dvd Mod LE LT Append HasAndthen HasUnion HasInter HasSdiff HasEquivₓ HasSubset HasSsubset HasEmptyc HasInsert HasSingleton HasSep HasMem Pow

-- ./././Mathport/Syntax/Translate/Basic.lean:1209:19: in notation_class: ./././Mathport/Syntax/Translate/Basic.lean:319:22: unsupported: too many args
attribute
  [«./././Mathport/Syntax/Translate/Basic.lean:1209:19: in notation_class: ./././Mathport/Syntax/Translate/Basic.lean:319:22: unsupported: too many args»]
  CoeSort

-- ./././Mathport/Syntax/Translate/Basic.lean:1209:19: in notation_class: ./././Mathport/Syntax/Translate/Basic.lean:319:22: unsupported: too many args
attribute
  [«./././Mathport/Syntax/Translate/Basic.lean:1209:19: in notation_class: ./././Mathport/Syntax/Translate/Basic.lean:319:22: unsupported: too many args»]
  CoeFun

/-- Returns the projection information of a structure. -/
unsafe def projections_info (l : List projection_data) (pref : Stringₓ) (str : Name) : tactic format := do
  let ⟨defaults, nondefaults⟩ ← return <| l.partitionMap fun s => if s.is_default then inl s else inr s
  let to_print ←
    defaults.mmap fun s =>
        toString <$>
          let prefix_str := if s.IsPrefix then "(prefix) " else ""
          f!"Projection {(← prefix_str)}{(← s.Name)}: {← s.expr}"
  let print2 := Stringₓ.join <| (nondefaults.map fun nm : projection_data => toString nm.1).intersperse ", "
  let to_print :=
    to_print ++
      if nondefaults.length = 0 then [] else ["No lemmas are generated for the projections: " ++ print2 ++ "."]
  let to_print := Stringₓ.join <| to_print.intersperse "\n        > "
  return
      f! "[simps] > {pref } {str }:
                > {to_print}"

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Auxiliary function of `get_composite_of_projections`. -/
unsafe def get_composite_of_projections_aux :
    ∀ (str : Name) (proj : Stringₓ) (x : expr) (pos : List ℕ) (args : List expr), tactic (expr × List ℕ)
  | str, proj, x, Pos, args => do
    let e ← get_env
    let projs ← e.structure_fields str
    let proj_info := projs.mapWithIndex fun n p => (fun x => (x, n, p)) <$> proj.getRest ("_" ++ p.last)
    when (proj_info id = []) <|
        "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
    let (proj_rest, index, proj_nm) ← return (proj_info.filterMap id).ilast
    let str_d ← e.get str
    let proj_e : expr := const (str ++ proj_nm) str_d.univ_levels
    let proj_d ← e.get (str ++ proj_nm)
    let type ← infer_type x
    let params := get_app_args type
    let univs := proj_d.univ_params.zip type.get_app_fn.univ_levels
    let new_x := (proj_e.instantiate_univ_params univs).mk_app <| params ++ [x]
    let new_pos := Pos ++ [index]
    if proj_rest then return (new_x args, new_pos)
      else do
        let type ← infer_type new_x
        let (type_args, tgt) ← open_pis_whnf type
        let new_str := tgt
        get_composite_of_projections_aux new_str proj_rest (new_x type_args) new_pos (args ++ type_args)

/-- Given a structure `str` and a projection `proj`, that could be multiple nested projections
  (separated by `_`), returns an expression that is the composition of these projections and a
  list of natural numbers, that are the projection numbers of the applied projections. -/
unsafe def get_composite_of_projections (str : Name) (proj : Stringₓ) : tactic (expr × List ℕ) := do
  let e ← get_env
  let str_d ← e.get str
  let str_e : expr := const str str_d.univ_levels
  let type ← infer_type str_e
  let (type_args, tgt) ← open_pis_whnf type
  let str_ap := str_e.mk_app type_args
  let x ← mk_local' `x BinderInfo.default str_ap
  get_composite_of_projections_aux str ("_" ++ proj) x [] <| type_args ++ [x]

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Get the projections used by `simps` associated to a given structure `str`.

  The returned information is also stored in a parameter of the attribute `@[_simps_str]`, which
  is given to `str`. If `str` already has this attribute, the information is read from this
  attribute instead. See the documentation for this attribute for the data this tactic returns.

  The returned universe levels are the universe levels of the structure. For the projections there
  are three cases
  * If the declaration `{structure_name}.simps.{projection_name}` has been declared, then the value
    of this declaration is used (after checking that it is definitionally equal to the actual
    projection. If you rename the projection name, the declaration should have the *new* projection
    name.
  * You can also declare a custom projection that is a composite of multiple projections.
  * Otherwise, for every class with the `notation_class` attribute, and the structure has an
    instance of that notation class, then the projection of that notation class is used for the
    projection that is definitionally equal to it (if there is such a projection).
    This means in practice that coercions to function types and sorts will be used instead of
    a projection, if this coercion is definitionally equal to a projection. Furthermore, for
    notation classes like `has_mul` and `has_zero` those projections are used instead of the
    corresponding projection.
    Projections for coercions and notation classes are not automatically generated if they are
    composites of multiple projections (for example when you use `extend` without the
    `old_structure_cmd`).
  * Otherwise, the projection of the structure is chosen.
    For example: ``simps_get_raw_projections env `prod`` gives the default projections
```
  ([u, v], [prod.fst.{u v}, prod.snd.{u v}])
```
    while ``simps_get_raw_projections env `equiv`` gives
```
  ([u_1, u_2], [λ α β, coe_fn, λ {α β} (e : α ≃ β), ⇑(e.symm), left_inv, right_inv])
```
    after declaring the coercion from `equiv` to function and adding the declaration
```
  def equiv.simps.inv_fun {α β} (e : α ≃ β) : β → α := e.symm
```

  Optionally, this command accepts three optional arguments:
  * If `trace_if_exists` the command will always generate a trace message when the structure already
    has the attribute `@[_simps_str]`.
  * The `rules` argument accepts a list of pairs `sum.inl (old_name, new_name)`. This is used to
    change the projection name `old_name` to the custom projection name `new_name`. Example:
    for the structure `equiv` the projection `to_fun` could be renamed `apply`. This name will be
    used for parsing and generating projection names. This argument is ignored if the structure
    already has an existing attribute. If an element of `rules` is of the form `sum.inr name`, this
    means that the projection `name` will not be applied by default.
  * if `trc` is true, this tactic will trace information.
-/
-- if performance becomes a problem, possible heuristic: use the names of the projections to
-- skip all classes that don't have the corresponding field.
unsafe def simps_get_raw_projections (e : environment) (str : Name) (trace_if_exists : Bool := false)
    (rules : List ProjectionRule := []) (trc := false) : tactic (List Name × List projection_data) := do
  let trc := trc || is_trace_enabled_for `simps.verbose
  let has_attr ← has_attribute' `_simps_str str
  if has_attr then do
      let data ← simps_str_attr str
      -- We always print the projections when they already exists and are called by
            -- `initialize_simps_projections`.
            when
            (trace_if_exists || is_trace_enabled_for `simps.verbose) <|
          projections_info data.2 "Already found projection information for structure" str >>= trace
      return data
    else do
      when trc
          (← do
            dbg_trace "[simps] > generating projection information for structure {← str}.")
      when_tracing `simps.debug
          (← do
            dbg_trace "[simps] > Applying the rules {← rules}.")
      let d_str ← e str
      let raw_univs := d_str
      let raw_levels := level.param <$> raw_univs
      let projs
        ←/- Figure out projections, including renamings. The information for a projection is (before we
                figure out the `expr` of the projection:
                `(original name, given name, is default, is prefix)`.
                The first projections are always the actual projections of the structure, but `rules` could
                specify custom projections that are compositions of multiple projections. -/
            e
            str
      let projs : List parsed_projection_data := projs fun nm => ⟨nm, nm, tt, ff⟩
      let projs : List parsed_projection_data :=
        rules
          (fun projs rule =>
            match rule with
            | (inl (old_nm, new_nm), is_prefix) =>
              if old_nm ∈ projs fun x => x then
                projs fun proj => if proj = old_nm then { proj with new_name := new_nm, IsPrefix } else proj
              else projs ++ [⟨old_nm, new_nm, tt, is_prefix⟩]
            | (inr nm, is_prefix) =>
              if nm ∈ projs fun x => x then
                projs fun proj => if proj = nm then { proj with is_default := ff, IsPrefix } else proj
              else projs ++ [⟨nm, nm, ff, is_prefix⟩])
          projs
      when_tracing `simps.debug
          (← do
            dbg_trace "[simps] > Projection info after applying the rules: {← projs}.")
      when ¬(projs fun x => x : List Name).Nodup <|
          fail <|
            "Invalid projection names. Two projections have the same name.\nThis is likely because a custom composition of projections was given the same name as an " ++
                "existing projection. Solution: rename the existing projection (before renaming the custom " ++
              "projection)."
      let raw_exprs_and_nrs
        ←/- Define the raw expressions for the projections, by default as the projections
                (as an expression), but this can be overriden by the user. -/
            projs
            fun ⟨orig_nm, new_nm, _, _⟩ => do
            let (raw_expr, nrs) ← get_composite_of_projections str orig_nm
            let custom_proj ←
              (do
                    let decl ← e (str ++ `simps ++ new_nm)
                    let custom_proj := decl <| decl raw_levels
                    when trc
                        (← do
                          dbg_trace "[simps] > found custom projection for {(← new_nm)}:
                                    > {← custom_proj}")
                    return custom_proj) <|>
                  return raw_expr
            is_def_eq custom_proj
                  raw_expr <|>-- if the type of the expression is different, we show a different error message, because
              -- that is more likely going to be helpful.
              do
                let custom_proj_type ← infer_type custom_proj
                let raw_expr_type ← infer_type raw_expr
                let b ← succeeds (is_def_eq custom_proj_type raw_expr_type)
                if b then
                    "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
                  else
                    "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
            return (custom_proj, nrs)
      let raw_exprs := raw_exprs_and_nrs Prod.fst
      let-- Check for other coercions and type-class arguments to use as projections instead.
        (args, _)
        ← open_pis d_str
      let e_str := (expr.const str raw_levels).mk_app args
      let automatic_projs ← attribute.get_instances `notation_class
      let raw_exprs ←
        automatic_projs
            (fun (raw_exprs : List expr) class_nm =>
              (/- For this class, find the projection. `raw_expr` is the projection found applied to `args`,
                        and `lambda_raw_expr` has the arguments `args` abstracted. -/
                -- Note: `expr.bind_lambda` doesn't give the correct type
                /- Use this as projection, if the function reduces to a projection, and this projection has
                        not been overrriden by the user. -/
                do
                  let (is_class, proj_nm) ← notation_class_attr class_nm
                  let proj_nm ← proj_nm <|> (e class_nm).map List.headₓ
                  let (raw_expr, lambda_raw_expr) ←
                    if is_class then do
                        guardₓ <| args = 1
                        let e_inst_type := (const class_nm raw_levels).mk_app args
                        let (hyp, e_inst) ← try_for 1000 (mk_conditional_instance e_str e_inst_type)
                        let raw_expr ← mk_mapp proj_nm [args, e_inst]
                        clear hyp
                        let raw_expr_lambda ← lambdas [hyp] raw_expr
                        return (raw_expr, raw_expr_lambda args)
                      else do
                        let e_inst_type ← to_expr (((const class_nm []).app (pexpr.of_expr e_str)).app (pquote.1 _))
                        let e_inst ← try_for 1000 (mk_instance e_inst_type)
                        let raw_expr ← mk_mapp proj_nm [e_str, none, e_inst]
                        return (raw_expr, raw_expr args)
                  let raw_expr_whnf ← whnf raw_expr
                  let relevant_proj := raw_expr_whnf
                  guardₓ <| projs fun x => x.1 = relevant_proj ∧ ¬e (str ++ `simps ++ x)
                  let pos := projs fun x => x.1 = relevant_proj
                  when trc
                      (← do
                        dbg_trace "        > using {(← proj_nm)} instead of the default projection {← relevant_proj}.")
                  when_tracing `simps.debug
                      (← do
                        dbg_trace "[simps] > The raw projection is:
                            {← lambda_raw_expr}")
                  return <| raw_exprs Pos lambda_raw_expr) <|>
                return raw_exprs)
            raw_exprs
      let positions := raw_exprs_and_nrs Prod.snd
      let proj_names := projs fun x => x
      let defaults := projs fun x => x
      let prefixes := projs fun x => x
      let projs := proj_names projection_data.mk raw_exprs positions defaults prefixes
      let projs
        ←-- make all proof non-default.
            projs
            fun proj => is_proof proj >>= fun b => return <| if b then { proj with is_default := ff } else proj
      when trc <| projections_info projs "generated projections for" str >>= trace
      simps_str_attr str (raw_univs, projs) tt
      when_tracing `simps.debug
          (← do
            dbg_trace "[simps] > Generated raw projection data: 
              {← (raw_univs, projs)}")
      return (raw_univs, projs)

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- Parse a rule for `initialize_simps_projections`. It is either `<name>→<name>` or `-<name>`,
  possibly following by `as_prefix`.-/
unsafe def simps_parse_rule : parser ProjectionRule :=
  Prod.mk <$> ((fun x y => inl (x, y)) <$> ident <*> (tk "->" >> ident) <|> inr <$> (tk "-" >> ident)) <*>
    is_some <$> «expr ?» (tk "as_prefix")

library_note "custom simps projection"/-- You can specify custom projections for the `@[simps]` attribute.
To do this for the projection `my_structure.original_projection` by adding a declaration
`my_structure.simps.my_projection` that is definitionally equal to
`my_structure.original_projection` but has the projection in the desired (simp-normal) form.
Then you can call
```
initialize_simps_projections (original_projection → my_projection, ...)
```
to register this projection. See `initialize_simps_projections_cmd` for more information.

You can also specify custom projections that are definitionally equal to a composite of multiple
projections. This is often desirable when extending structures (without `old_structure_cmd`).

`has_coe_to_fun` and notation class (like `has_mul`) instances will be automatically used, if they
are definitionally equal to a projection of the structure (but not when they are equal to the
composite of multiple projections).
-/


-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr *»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- This command specifies custom names and custom projections for the simp attribute `simps_attr`.
* You can specify custom names by writing e.g.
  `initialize_simps_projections equiv (to_fun → apply, inv_fun → symm_apply)`.
* See Note [custom simps projection] and the examples below for information how to declare custom
  projections.
* If no custom projection is specified, the projection will be `coe_fn`/`⇑` if a `has_coe_to_fun`
  instance has been declared, or the notation of a notation class (like `has_mul`) if such an
  instance is available. If none of these cases apply, the projection itself will be used.
* You can disable a projection by default by running
  `initialize_simps_projections equiv (-inv_fun)`
  This will ensure that no simp lemmas are generated for this projection,
  unless this projection is explicitly specified by the user.
* If you want the projection name added as a prefix in the generated lemma name, you can add the
  `as_prefix` modifier:
  `initialize_simps_projections equiv (to_fun → coe as_prefix)`
  Note that this does not influence the parsing of projection names: if you have a declaration
  `foo` and you want to apply the projections `snd`, `coe` (which is a prefix) and `fst`, in that
  order you can run `@[simps snd_coe_fst] def foo ...` and this will generate a lemma with the
  name `coe_foo_snd_fst`.
  * Run `initialize_simps_projections?` (or `set_option trace.simps.verbose true`)
  to see the generated projections.
* You can declare a new name for a projection that is the composite of multiple projections, e.g.
  ```
    structure A := (proj : ℕ)
    structure B extends A
    initialize_simps_projections? B (to_A_proj → proj, -to_A)
  ```
  You can also make your custom projection that is definitionally equal to a composite of
  projections. In this case, coercions and notation classes are not automatically recognized, and
  should be manually given by giving a custom projection.
  This is especially useful when extending a structure (without `old_structure_cmd`).
  In the above example, it is desirable to add `-to_A`, so that `@[simps]` doesn't automatically
  apply the `B.to_A` projection and then recursively the `A.proj` projection in the lemmas it
  generates. If you want to get both the `foo_proj` and `foo_to_A` simp lemmas, you can use
  `@[simps, simps to_A]`.
* Running `initialize_simps_projections my_struc` without arguments is not necessary, it has the
  same effect if you just add `@[simps]` to a declaration.
* If you do anything to change the default projections, make sure to call either `@[simps]` or
  `initialize_simps_projections` in the same file as the structure declaration. Otherwise, you might
  have a file that imports the structure, but not your custom projections.

Some common uses:
* If you define a new homomorphism-like structure (like `mul_hom`) you can just run
  `initialize_simps_projections` after defining the `has_coe_to_fun` instance
  ```
    instance {mM : has_mul M} {mN : has_mul N} : has_coe_to_fun (M →ₙ* N) := ...
    initialize_simps_projections mul_hom (to_fun → apply)
  ```
  This will generate `foo_apply` lemmas for each declaration `foo`.
* If you prefer `coe_foo` lemmas that state equalities between functions, use
  `initialize_simps_projections mul_hom (to_fun → coe as_prefix)`
  In this case you have to use `@[simps {fully_applied := ff}]` or equivalently `@[simps as_fn]`
  whenever you call `@[simps]`.
* You can also initialize to use both, in which case you have to choose which one to use by default,
  by using either of the following
  ```
    initialize_simps_projections mul_hom (to_fun → apply, to_fun → coe, -coe as_prefix)
    initialize_simps_projections mul_hom (to_fun → apply, to_fun → coe as_prefix, -apply)
  ```
  In the first case, you can get both lemmas using `@[simps, simps coe as_fn]` and in the second
  case you can get both lemmas using `@[simps as_fn, simps apply]`.
* If your new homomorphism-like structure extends another structure (without `old_structure_cmd`)
  (like `rel_embedding`), then you have to specify explicitly that you want to use a coercion
  as a custom projection. For example
  ```
    def rel_embedding.simps.apply (h : r ↪r s) : α → β := h
    initialize_simps_projections rel_embedding (to_embedding_to_fun → apply, -to_embedding)
  ```
* If you have an isomorphism-like structure (like `equiv`) you often want to define a custom
  projection for the inverse:
  ```
    def equiv.simps.symm_apply (e : α ≃ β) : β → α := e.symm
    initialize_simps_projections equiv (to_fun → apply, inv_fun → symm_apply)
  ```
-/
@[user_command]
unsafe def initialize_simps_projections_cmd (_ : parse <| tk "initialize_simps_projections") : parser Unit := do
  let env ← get_env
  let trc ← is_some <$> «expr ?» (tk "?")
  let ns ← «expr *» (Prod.mk <$> ident <*> «expr ?» (tk "(" >> sep_by (tk ",") simps_parse_rule <* tk ")"))
  ns fun data => do
      let nm ← resolve_constant data.1
      simps_get_raw_projections env nm tt (data.2.getOrElse []) trc

add_tactic_doc
  { Name := "initialize_simps_projections", category := DocCategory.cmd,
    declNames := [`initialize_simps_projections_cmd], tags := ["simplification"] }

/-- Configuration options for the `@[simps]` attribute.
  * `attrs` specifies the list of attributes given to the generated lemmas. Default: ``[`simp]``.
    The attributes can be either basic attributes, or user attributes without parameters.
    There are two attributes which `simps` might add itself:
    * If ``[`simp]`` is in the list, then ``[`_refl_lemma]`` is added automatically if appropriate.
    * If the definition is marked with `@[to_additive ...]` then all generated lemmas are marked
      with `@[to_additive]`. This is governed by the `add_additive` configuration option.
  * if `simp_rhs` is `tt` then the right-hand-side of the generated lemmas will be put in
    simp-normal form. More precisely: `dsimp, simp` will be called on all these expressions.
    See note [dsimp, simp].
  * `type_md` specifies how aggressively definitions are unfolded in the type of expressions
    for the purposes of finding out whether the type is a function type.
    Default: `instances`. This will unfold coercion instances (so that a coercion to a function type
    is recognized as a function type), but not declarations like `set`.
  * `rhs_md` specifies how aggressively definition in the declaration are unfolded for the purposes
    of finding out whether it is a constructor.
    Default: `none`
    Exception: `@[simps]` will automatically add the options
    `{rhs_md := semireducible, simp_rhs := tt}` if the given definition is not a constructor with
    the given reducibility setting for `rhs_md`.
  * If `fully_applied` is `ff` then the generated `simp` lemmas will be between non-fully applied
    terms, i.e. equalities between functions. This does not restrict the recursive behavior of
    `@[simps]`, so only the "final" projection will be non-fully applied.
    However, it can be used in combination with explicit field names, to get a partially applied
    intermediate projection.
  * The option `not_recursive` contains the list of names of types for which `@[simps]` doesn't
    recursively apply projections. For example, given an equivalence `α × β ≃ β × α` one usually
    wants to only apply the projections for `equiv`, and not also those for `×`. This option is
    only relevant if no explicit projection names are given as argument to `@[simps]`.
  * The option `trace` is set to `tt` when you write `@[simps?]`. In this case, the attribute will
    print all generated lemmas. It is almost the same as setting the option `trace.simps.verbose`,
    except that it doesn't print information about the found projections.
  * if `add_additive` is `some nm` then `@[to_additive]` is added to the generated lemma. This
    option is automatically set to `tt` when the original declaration was tagged with
    `@[to_additive, simps]` (in that order), where `nm` is the additive name of the original
    declaration.
-/
structure SimpsCfg where
  attrs := [`simp]
  simpRhs := false
  typeMd := Transparency.instances
  rhsMd := Transparency.none
  fullyApplied := true
  notRecursive := [`prod, `pprod]
  trace := false
  addAdditive := @none Name
  deriving has_reflect, Inhabited

/-- A common configuration for `@[simps]`: generate equalities between functions instead equalities
  between fully applied expressions. -/
def asFn : SimpsCfg where fullyApplied := false

/-- A common configuration for `@[simps]`: don't tag the generated lemmas with `@[simp]`. -/
def lemmasOnly : SimpsCfg where attrs := []

/-- Get the projections of a structure used by `@[simps]` applied to the appropriate arguments.
  Returns a list of tuples
  ```
  (corresponding right-hand-side, given projection name, projection expression, projection numbers,
    used by default, is prefix)
  ```
  (where all fields except the first are packed in a `projection_data` structure)
  one for each projection. The given projection name is the name for the projection used by the user
  used to generate (and parse) projection names. For example, in the structure

  Example 1: ``simps_get_projection_exprs env `(α × β) `(⟨x, y⟩)`` will give the output
  ```
    [(`(x), `fst, `(@prod.fst.{u v} α β), [0], tt, ff),
     (`(y), `snd, `(@prod.snd.{u v} α β), [1], tt, ff)]
  ```

  Example 2: ``simps_get_projection_exprs env `(α ≃ α) `(⟨id, id, λ _, rfl, λ _, rfl⟩)``
  will give the output
  ```
    [(`(id), `apply, `(coe), [0], tt, ff),
     (`(id), `symm_apply, `(λ f, ⇑f.symm), [1], tt, ff),
     ...,
     ...]
  ```
-/
unsafe def simps_get_projection_exprs (e : environment) (tgt : expr) (rhs : expr) (cfg : SimpsCfg) :
    tactic <| List <| expr × projection_data := do
  let params := get_app_args tgt
  ((-- the parameters of the structure
            params <|
            (get_app_args rhs).take params).mmap'
        fun ⟨a, b⟩ => is_def_eq a b) <|>
      fail "unreachable code (1)"
  let str := tgt.get_app_fn.const_name
  let rhs_args := (get_app_args rhs).drop params.length
  let-- the fields of the object
    (raw_univs, proj_data)
    ← simps_get_raw_projections e str false [] cfg.trace
  let univs := raw_univs.zip tgt.get_app_fn.univ_levels
  let new_proj_data : List <| expr × projection_data :=
    proj_data.map fun proj =>
      (rhs_args.inth proj.proj_nrs.head,
        { proj with expr := (proj.expr.instantiate_univ_params univs).instantiate_lambdas_or_apps params,
          proj_nrs := proj.proj_nrs.tail })
  return new_proj_data

/-- Add a lemma with `nm` stating that `lhs = rhs`. `type` is the type of both `lhs` and `rhs`,
  `args` is the list of local constants occurring, and `univs` is the list of universe variables. -/
unsafe def simps_add_projection (nm : Name) (type lhs rhs : expr) (args : List expr) (univs : List Name)
    (cfg : SimpsCfg) : tactic Unit := do
  when_tracing `simps.debug
      (← do
        dbg_trace "[simps] > Planning to add the equality
                  > {(← lhs)} = ({(← rhs)} : {← type})")
  let lvl ← get_univ_level type
  let-- simplify `rhs` if `cfg.simp_rhs` is true
    (rhs, prf)
    ←
    (do
          guardₓ cfg
          let rhs' ← rhs.dsimp { failIfUnchanged := false }
          when_tracing `simps.debug <|
              when (rhs ≠ rhs')
                (← do
                  dbg_trace "[simps] > `dsimp` simplified rhs to
                            > {← rhs'}")
          let (rhsprf1, rhsprf2, ns) ← rhs'.simp { failIfUnchanged := false }
          when_tracing `simps.debug <|
              when (rhs' ≠ rhsprf1)
                (← do
                  dbg_trace "[simps] > `simp` simplified rhs to
                            > {← rhsprf1}")
          return (Prod.mk rhsprf1 rhsprf2)) <|>
        return (rhs, const `eq.refl [lvl] type lhs)
  let eq_ap := const `eq [lvl] type lhs rhs
  let decl_name ← get_unused_decl_name nm
  let decl_type := eq_ap.pis args
  let decl_value := prf.lambdas args
  let decl := declaration.thm decl_name univs decl_type (pure decl_value)
  when cfg
      (← do
        dbg_trace "[simps] > adding projection {(← decl_name)}:
                  > {← decl_type}")
  decorate_error ("Failed to add projection lemma " ++ decl_name ++ ". Nested error:") <| add_decl decl
  let b ← succeeds <| is_def_eq lhs rhs
  when (b ∧ `simp ∈ cfg) (set_basic_attribute `_refl_lemma decl_name tt)
  cfg fun nm => set_attribute nm decl_name tt
  when cfg <| to_additive.attr decl_name ⟨ff, cfg, cfg, none, tt⟩ tt

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Derive lemmas specifying the projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  `to_apply` is non-empty after a custom projection that is a composition of multiple projections
  was just used. In that case we need to apply these projections before we continue changing lhs. -/
unsafe def simps_add_projections :
    ∀ (e : environment) (nm : Name) (type lhs rhs : expr) (args : List expr) (univs : List Name) (must_be_str : Bool)
      (cfg : SimpsCfg) (todo : List Stringₓ) (to_apply : List ℕ), tactic Unit
  | e, nm, type, lhs, rhs, args, univs, must_be_str, cfg, todo, to_apply => do
    -- we don't want to unfold non-reducible definitions (like `set`) to apply more arguments
        when_tracing
        `simps.debug
        (← do
          dbg_trace "[simps] > Type of the expression before normalizing: {← type}")
    let (type_args, tgt) ← open_pis_whnf type cfg.typeMd
    when_tracing `simps.debug
        (← do
          dbg_trace "[simps] > Type after removing pi's: {← tgt}")
    let tgt ← whnf tgt
    when_tracing `simps.debug
        (← do
          dbg_trace "[simps] > Type after reduction: {← tgt}")
    let new_args := args ++ type_args
    let lhs_ap := lhs.instantiate_lambdas_or_apps type_args
    let rhs_ap := rhs.instantiate_lambdas_or_apps type_args
    let str := tgt.get_app_fn.const_name
    let-- We want to generate the current projection if it is in `todo`
    todo_next := todo.filter (· ≠ "")
    /- Don't recursively continue if `str` is not a structure or if the structure is in
            `not_recursive`. -/
        if e str ∧ ¬(todo = [] ∧ str ∈ cfg ∧ ¬must_be_str) then do
        let [intro] ← return <| e str | fail "unreachable code (3)"
        let rhs_whnf ← whnf rhs_ap cfg
        let (rhs_ap, todo_now)
          ←-- `todo_now` means that we still have to generate the current simp lemma
              if ¬is_constant_of rhs_ap intro ∧ is_constant_of rhs_whnf intro then
              /- If this was a desired projection, we want to apply it before taking the whnf.
                          However, if the current field is an eta-expansion (see below), we first want
                          to eta-reduce it and only then construct the projection.
                          This makes the flow of this function messy. -/
                  when
                  ("" ∈ todo ∧ to_apply = [])
                  (if cfg then simps_add_projection nm tgt lhs_ap rhs_ap new_args univs cfg
                  else simps_add_projection nm type lhs rhs args univs cfg) >>
                return (rhs_whnf, ff)
            else return (rhs_ap, "" ∈ todo ∧ to_apply = [])
        if is_constant_of (get_app_fn rhs_ap) intro then do
            let proj_info
              ←-- if the value is a constructor application
                  simps_get_projection_exprs
                  e tgt rhs_ap cfg
            when_tracing `simps.debug
                (← do
                  dbg_trace "[simps] > Raw projection information:
                      {← proj_info}")
            let eta ← rhs_ap
            let-- check whether `rhs_ap` is an eta-expansion
            rhs_ap := eta rhs_ap
            -- eta-reduce `rhs_ap`
                  /- As a special case, we want to automatically generate the current projection if `rhs_ap`
                          was an eta-expansion. Also, when this was a desired projection, we need to generate the
                          current projection if we haven't done it above. -/
                  when
                  (todo_now ∨ todo = [] ∧ eta ∧ to_apply = []) <|
                if cfg then simps_add_projection nm tgt lhs_ap rhs_ap new_args univs cfg
                else simps_add_projection nm type lhs rhs args univs cfg
            -- If we are in the middle of a composite projection.
                  when
                  (to_apply ≠ []) <|
                do
                let ⟨new_rhs, proj, proj_expr, proj_nrs, is_default, is_prefix⟩ ← return <| proj_info to_apply
                let new_type ← infer_type new_rhs
                when_tracing `simps.debug
                    (← do
                      dbg_trace "[simps] > Applying a custom composite projection. Current lhs:
                                >  {← lhs_ap}")
                simps_add_projections e nm new_type lhs_ap new_rhs new_args univs ff cfg todo to_apply
            /- We stop if no further projection is specified or if we just reduced an eta-expansion and we
                        automatically choose projections -/
                  when
                  ¬(to_apply ≠ [] ∨ todo = [""] ∨ eta ∧ todo = []) <|
                do
                let projs : List Name := proj_info fun x => x
                let todo := if to_apply = [] then todo_next else todo
                -- check whether all elements in `todo` have a projection as prefix
                      guardₓ
                      (todo fun x => projs fun proj => ("_" ++ proj).isPrefixOf x) <|>
                    let x := (todo fun x => projs fun proj => ¬("_" ++ proj).isPrefixOf x).iget
                    let simp_lemma := nm x
                    let needed_proj := (x '_').tail.head
                    "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
                proj_info fun proj_nr ⟨new_rhs, proj, proj_expr, proj_nrs, is_default, is_prefix⟩ => do
                    let new_type ← infer_type new_rhs
                    let new_todo := todo fun x => x ("_" ++ proj)
                    -- we only continue with this field if it is non-propositional or mentioned in todo
                          when
                          (is_default ∧ todo = [] ∨ new_todo ≠ []) <|
                        do
                        let new_lhs := proj_expr [lhs_ap]
                        let new_nm := nm proj is_prefix
                        let new_cfg :=
                          { cfg with addAdditive := cfg fun nm => nm (to_additive.guess_name proj) is_prefix }
                        when_tracing `simps.debug
                            (← do
                              dbg_trace "[simps] > Recursively add projections for:
                                        >  {← new_lhs}")
                        simps_add_projections e new_nm new_type new_lhs new_rhs new_args univs ff new_cfg new_todo
                            proj_nrs
          else-- if I'm about to run into an error, try to set the transparency for `rhs_md` higher.
              if cfg = transparency.none ∧ (must_be_str ∨ todo_next ≠ [] ∨ to_apply ≠ []) then do
              when cfg
                  (← do
                    dbg_trace "[simps] > The given definition is not a constructor application:
                              >   {← rhs_ap}
                              > Retrying with the options \{ rhs_md := semireducible, simp_rhs := tt}.")
              simps_add_projections e nm type lhs rhs args univs must_be_str
                  { cfg with rhsMd := semireducible, simpRhs := tt } todo to_apply
            else do
              when (to_apply ≠ []) <|
                  "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
              when must_be_str <|
                  "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
              when (todo_next ≠ []) <|
                  "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
              if cfg then simps_add_projection nm tgt lhs_ap rhs_ap new_args univs cfg
                else simps_add_projection nm type lhs rhs args univs cfg
      else do
        when must_be_str <|
            "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
        when (todo_next ≠ [] ∧ str ∉ cfg) <|
            let first_todo := todo_next
            "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
        if cfg then simps_add_projection nm tgt lhs_ap rhs_ap new_args univs cfg
          else simps_add_projection nm type lhs rhs args univs cfg

/-- `simps_tac` derives `simp` lemmas for all (nested) non-Prop projections of the declaration.
  If `todo` is non-empty, it will generate exactly the names in `todo`.
  If `short_nm` is true, the generated names will only use the last projection name.
  If `trc` is true, trace as if `trace.simps.verbose` is true. -/
unsafe def simps_tac (nm : Name) (cfg : SimpsCfg := {  }) (todo : List Stringₓ := []) (trc := false) : tactic Unit := do
  let e ← get_env
  let d ← e.get nm
  let lhs : expr := const d.to_name d.univ_levels
  let todo := todo.dedup.map fun proj => "_" ++ proj
  let cfg := { cfg with trace := cfg.trace || is_trace_enabled_for `simps.verbose || trc }
  let b ← has_attribute' `to_additive nm
  let cfg ←
    if b then do
        let dict ← to_additive.aux_attr.get_cache
        when cfg
            (← do
              dbg_trace "[simps] > @[to_additive] will be added to all generated lemmas.")
        return { cfg with addAdditive := dict nm }
      else return cfg
  simps_add_projections e nm d lhs d [] d tt cfg todo []

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- The parser for the `@[simps]` attribute. -/
unsafe def simps_parser : parser (Bool × List Stringₓ × SimpsCfg) := do
  -- note: we don't check whether the user has written a nonsense namespace in an argument.
        Prod.mk <$>
        is_some <$> «expr ?» (tk "?") <*>
      (Prod.mk <$> many (name.last <$> ident) <*> do
        let some e ← «expr ?» parser.pexpr | return {  }
        eval_pexpr SimpsCfg e)

/-- The `@[simps]` attribute automatically derives lemmas specifying the projections of this
declaration.

Example:
```lean
@[simps] def foo : ℕ × ℤ := (1, 2)
```
derives two `simp` lemmas:
```lean
@[simp] lemma foo_fst : foo.fst = 1
@[simp] lemma foo_snd : foo.snd = 2
```

* It does not derive `simp` lemmas for the prop-valued projections.
* It will automatically reduce newly created beta-redexes, but will not unfold any definitions.
* If the structure has a coercion to either sorts or functions, and this is defined to be one
  of the projections, then this coercion will be used instead of the projection.
* If the structure is a class that has an instance to a notation class, like `has_mul`, then this
  notation is used instead of the corresponding projection.
* You can specify custom projections, by giving a declaration with name
  `{structure_name}.simps.{projection_name}`. See Note [custom simps projection].

  Example:
  ```lean
  def equiv.simps.inv_fun (e : α ≃ β) : β → α := e.symm
  @[simps] def equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩
  ```
  generates
  ```
  @[simp] lemma equiv.trans_to_fun : ∀ {α β γ} (e₁ e₂) (a : α), ⇑(e₁.trans e₂) a = (⇑e₂ ∘ ⇑e₁) a
  @[simp] lemma equiv.trans_inv_fun : ∀ {α β γ} (e₁ e₂) (a : γ),
    ⇑((e₁.trans e₂).symm) a = (⇑(e₁.symm) ∘ ⇑(e₂.symm)) a
  ```

* You can specify custom projection names, by specifying the new projection names using
  `initialize_simps_projections`.
  Example: `initialize_simps_projections equiv (to_fun → apply, inv_fun → symm_apply)`.
  See `initialize_simps_projections_cmd` for more information.

* If one of the fields itself is a structure, this command will recursively create
  `simp` lemmas for all fields in that structure.
  * Exception: by default it will not recursively create `simp` lemmas for fields in the structures
    `prod` and `pprod`. You can give explicit projection names or change the value of
    `simps_cfg.not_recursive` to override this behavior.

  Example:
  ```lean
  structure my_prod (α β : Type*) := (fst : α) (snd : β)
  @[simps] def foo : prod ℕ ℕ × my_prod ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_snd_fst : foo.snd.fst = 3
  @[simp] lemma foo_snd_snd : foo.snd.snd = 4
  ```

* You can use `@[simps proj1 proj2 ...]` to only generate the projection lemmas for the specified
  projections.
* Recursive projection names can be specified using `proj1_proj2_proj3`.
  This will create a lemma of the form `foo.proj1.proj2.proj3 = ...`.

  Example:
  ```lean
  structure my_prod (α β : Type*) := (fst : α) (snd : β)
  @[simps fst fst_fst snd] def foo : prod ℕ ℕ × my_prod ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
  ```
  generates
  ```lean
  @[simp] lemma foo_fst : foo.fst = (1, 2)
  @[simp] lemma foo_fst_fst : foo.fst.fst = 1
  @[simp] lemma foo_snd : foo.snd = {fst := 3, snd := 4}
  ```
* If one of the values is an eta-expanded structure, we will eta-reduce this structure.

  Example:
  ```lean
  structure equiv_plus_data (α β) extends α ≃ β := (data : bool)
  @[simps] def bar {α} : equiv_plus_data α α := { data := tt, ..equiv.refl α }
  ```
  generates the following:
  ```lean
  @[simp] lemma bar_to_equiv : ∀ {α : Sort*}, bar.to_equiv = equiv.refl α
  @[simp] lemma bar_data : ∀ {α : Sort*}, bar.data = tt
  ```
  This is true, even though Lean inserts an eta-expanded version of `equiv.refl α` in the
  definition of `bar`.
* For configuration options, see the doc string of `simps_cfg`.
* The precise syntax is `('simps' ident* e)`, where `e` is an expression of type `simps_cfg`.
* `@[simps]` reduces let-expressions where necessary.
* When option `trace.simps.verbose` is true, `simps` will print the projections it finds and the
  lemmas it generates. The same can be achieved by using `@[simps?]`, except that in this case it
  will not print projection information.
* Use `@[to_additive, simps]` to apply both `to_additive` and `simps` to a definition, making sure
  that `simps` comes after `to_additive`. This will also generate the additive versions of all
  `simp` lemmas.
-/
/- If one of the fields is a partially applied constructor, we will eta-expand it
  (this likely never happens, so is not included in the official doc). -/
@[user_attribute]
unsafe def simps_attr : user_attribute Unit (Bool × List Stringₓ × SimpsCfg) where
  Name := `simps
  descr := "Automatically derive lemmas specifying the projections of this declaration."
  parser := simps_parser
  after_set :=
    some fun n _ persistent => do
      guardₓ persistent <|> fail "`simps` currently cannot be used as a local attribute"
      let (trc, todo, cfg) ← simps_attr.get_param n
      simps_tac n cfg todo trc

add_tactic_doc { Name := "simps", category := DocCategory.attr, declNames := [`simps_attr], tags := ["simplification"] }

