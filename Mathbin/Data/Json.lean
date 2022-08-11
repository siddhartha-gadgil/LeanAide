/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Tactic.Core

/-!
# Json serialization typeclass

This file provides helpers for serializing primitive types to json.

`@[derive non_null_json_serializable]` will make any structure json serializable; for instance,
```lean
@[derive non_null_json_serializable]
structure my_struct :=
(success : bool)
(verbose : ℕ := 0)
(extras : option string := none)
```
can parse `{"success": true}` as `my_struct.mk true 0 none`, and reserializing give
`{"success": true, "verbose": 0, "extras": null}`.

## Main definitions

* `json_serializable`: a typeclass for objects which serialize to json
* `json_serializable.to_json x`: convert `x` to json
* `json_serializable.of_json α j`: read `j` in as an `α`
-/


open Exceptional

unsafe instance :
    HasOrelse exceptional where orelse := fun α f g =>
    match f with
    | success x => success x
    | exception msg => g

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`of_json] []
/-- A class to indicate that a type is json serializable -/
unsafe class json_serializable (α : Type) where
  to_json : α → json
  of_json : json → exceptional α

/-- A class for types which never serialize to null -/
unsafe class non_null_json_serializable (α : Type) extends json_serializable α

export JsonSerializable (to_json of_json)

/-- Describe the type of a json value -/
unsafe def json.typename : json → Stringₓ
  | json.of_string _ => "string"
  | json.of_int _ => "number"
  | json.of_float _ => "number"
  | json.of_bool _ => "bool"
  | json.null => "null"
  | json.object _ => "object"
  | json.array _ => "array"

/-! ### Primitive types -/


unsafe instance : non_null_json_serializable Stringₓ where
  to_json := json.of_string
  of_json := fun j => do
    let json.of_string s ← success j | exception fun _ => f! "string expected, got {j.typename}"
    pure s

unsafe instance : non_null_json_serializable ℤ where
  to_json := fun z => json.of_int z
  of_json := fun j => do
    let json.of_int z ← success j |
      do
        let json.of_float f ← success j | exception fun _ => f! "number expected, got {j.typename}"
        exception fun _ => f!"number must be integral"
    pure z

unsafe instance : non_null_json_serializable native.float where
  to_json := fun f => json.of_float f
  of_json := fun j => do
    let json.of_int z ← success j |
      do
        let json.of_float f ← success j | exception fun _ => f! "number expected, got {j.typename}"
        pure f
    pure z

unsafe instance : non_null_json_serializable Bool where
  to_json := fun b => json.of_bool b
  of_json := fun j => do
    let json.of_bool b ← success j | exception fun _ => f! "boolean expected, got {j.typename}"
    pure b

unsafe instance : json_serializable PUnit where
  to_json := fun u => json.null
  of_json := fun j => do
    let json.null ← success j | exception fun _ => f! "null expected, got {j.typename}"
    pure ()

unsafe instance {α} [json_serializable α] : non_null_json_serializable (List α) where
  to_json := fun l => json.array (l.map to_json)
  of_json := fun j => do
    let json.array l ← success j | exception fun _ => f! "array expected, got {j.typename}"
    l (of_json α)

unsafe instance {α} [json_serializable α] : json_serializable (Rbmap Stringₓ α) where
  to_json := fun m => json.object (m.toList.map fun x => (x.1, to_json x.2))
  of_json := fun j => do
    let json.object l ← success j | exception fun _ => f! "object expected, got {j.typename}"
    let l ←
      l.mmap fun x : Stringₓ × json => do
          let x2 ← of_json α x.2
          pure (x.1, x2)
    l
        (fun m x => do
          let none ← pure (m x.1) | exception fun _ => f! "duplicate key {x.1}"
          pure (m x.1 x.2))
        (mkRbmap _ _)

/-! ### Basic coercions -/


unsafe instance : non_null_json_serializable ℕ where
  to_json := fun n => to_json (n : ℤ)
  of_json := fun j => do
    let Int.ofNat n ← of_json ℤ j | exception fun _ => f!"must be non-negative"
    pure n

unsafe instance {n : ℕ} : non_null_json_serializable (Finₓ n) where
  to_json := fun i => to_json i.val
  of_json := fun j => do
    let i ← of_json ℕ j
    if h : i < n then pure ⟨i, h⟩ else exception fun _ => f! "must be less than {n}"

unsafe instance {α : Type} [json_serializable α] (p : α → Prop) [DecidablePred p] : json_serializable (Subtype p) where
  to_json := fun x => to_json (x : α)
  of_json := fun j => do
    let i ← of_json α j
    if h : p i then pure (Subtype.mk i h) else exception fun _ => f!"condition does not hold"

/-- Note this only makes sense on types which do not themselves serialize to `null` -/
unsafe instance {α} [non_null_json_serializable α] : json_serializable (Option α) where
  to_json := Option.elimₓ json.null to_json
  of_json := fun j => do
    of_json PUnit j >> pure none <|> some <$> of_json α j

open Tactic Expr

/-- Flatten a list of (p)exprs into a (p)expr forming a list of type `list t`. -/
unsafe def list.to_expr {elab : Bool} (t : expr elab) (l : level) : List (expr elab) → expr elab
  | [] => expr.app (expr.const `list.nil [l]) t
  | x :: xs => (((expr.const `list.cons [l]).app t).app x).app xs.to_expr

/-- Begin parsing fields -/
unsafe def json_serializable.field_starter (j : json) : exceptional (List (Stringₓ × json)) := do
  let json.object p ← pure j | exception fun _ => f! "object expected, got {j.typename}"
  pure p

/-- Check a field exists and is unique -/
unsafe def json_serializable.field_get (l : List (Stringₓ × json)) (s : Stringₓ) :
    exceptional (Option json × List (Stringₓ × json)) :=
  let (p, n) := l.partition fun x => Prod.fst x = s
  match p with
  | [] => pure (none, n)
  | [x] => pure (some x.2, n)
  | x :: xs => exception fun _ => f! "duplicate {s} field"

/-- Check no fields remain -/
unsafe def json_serializable.field_terminator (l : List (Stringₓ × json)) : exceptional Unit := do
  let [] ← pure l | exception fun _ => f! "unexpected fields {l.map Prod.fst}"
  pure ()

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- ``((c_name, c_fun), [(p_name, p_fun), ...]) ← get_constructor_and_projections `(struct n)``
gets the names and partial invocations of the constructor and projections of a structure -/
unsafe def get_constructor_and_projections (t : expr) : tactic (Name × (Name × expr) × List (Name × expr)) := do
  let (const I ls, args) ← pure (get_app_fn_args t)
  let env ← get_env
  let [ctor] ← pure (env.constructors_of I)
  let ctor ←
    do
      let d ← get_decl ctor
      let a := @expr.const true ctor <| d.univ_params.map level.param
      pure (ctor, a args)
  let ctor_type ← infer_type ctor.2
  let tt ← pure ctor_type.is_pi | pure (I, ctor, [])
  let some fields ← pure (env.structure_fields I) |
    "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
  let projs ←
    fields.mmap fun f => do
        let d ← get_decl (I ++ f)
        let a := @expr.const true (I ++ f) <| d.univ_params.map level.param
        pure (f, a args)
  pure (I, ctor, projs)

/-- Generate an expression that builds a term of type `t` (which is itself a parametrization of
the structure `struct_name`) using the expressions resolving to parsed fields in `vars` and the
expressions resolving to unparsed `option json` objects in `js`. This can handled
dependently-typed and defaulted (via `:=` which for structures is not the same as `opt_param`)
fields. -/
unsafe def of_json_helper (struct_name : Name) (t : expr) :
    ∀ (vars : List (Name × pexpr)) (js : List (Name × Option expr)), tactic expr
  | vars, [] => do
    let-- allow this partial constructor if `to_expr` allows it
    struct := pexpr.mk_structure_instance ⟨some struct_name, vars.map Prod.fst, vars.map Prod.snd, []⟩
    to_expr (pquote.1 (pure (%%ₓstruct) : exceptional (%%ₓt)))
  | vars, (fname, some fj) :: js => do
    let u
      ←-- data fields
        mk_meta_univ
    let ft : expr ← mk_meta_var (expr.sort u)
    let f_binder ← mk_local' fname BinderInfo.default ft
    let new_vars := vars.concat (fname, to_pexpr f_binder)
    let with_field ← of_json_helper new_vars js >>= tactic.lambdas [f_binder]
    let without_field ←
      of_json_helper vars js <|>
          to_expr (pquote.1 (exception fun o => f!"field {%%ₓquote.1 fname} is required" : exceptional (%%ₓt)))
    to_expr
        (pquote.1
          (Option.mmapₓ (of_json _) (%%ₓfj) >>= Option.elimₓ (%%ₓwithout_field) (%%ₓwith_field) : exceptional (%%ₓt)))
  | vars,
    (fname, none) :: js =>-- try a default value
        of_json_helper
        vars js <|>
      do
      let u
        ←-- otherwise, use decidability
          mk_meta_univ
      let ft ← mk_meta_var (expr.sort u)
      let f_binder ← mk_local' fname BinderInfo.default ft
      let new_vars := vars.concat (fname, to_pexpr f_binder)
      let with_field ← of_json_helper new_vars js >>= tactic.lambdas [f_binder]
      to_expr (pquote.1 (dite _ (%%ₓwith_field) fun _ => exception fun _ => f!"condition does not hold"))

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- A derive handler to serialize structures by their fields.

For the following structure:
```lean
structure has_default : Type :=
(x : ℕ := 2)
(y : fin x.succ := 3 * fin.of_nat x)
(z : ℕ := 3)
```
this generates an `of_json` parser along the lines of

```lean
meta def has_default.of_json (j : json) : exceptional (has_default) :=
do
  p ← json_serializable.field_starter j,
  (f_y, p) ← json_serializable.field_get p "y",
  (f_z, p) ← json_serializable.field_get p "z",
  f_y.mmap (of_json _) >>= option.elim
    (f_z.mmap (of_json _) >>= option.elim
      (pure {has_default.})
      (λ z, pure {has_default. z := z})
    )
    (λ y, f_z.mmap (of_json _) >>= option.elim
        (pure {has_default.})
        (λ z, pure {has_default. y := y, z := z})
    )
```
-/
@[derive_handler]
unsafe def non_null_json_serializable_handler : derive_handler :=
  instance_derive_handler `` non_null_json_serializable <| do
    intros
    let quote.1 (non_null_json_serializable (%%ₓe)) ← target >>= whnf
    let (struct_name, (ctor_name, ctor), fields) ← get_constructor_and_projections e
    refine
        (pquote.1
          (@non_null_json_serializable.mk (%%ₓe)
            ⟨fun x => json.object _, fun j => json_serializable.field_starter j >>= _⟩))
    let x
      ←-- the forward direction
          get_local
          `x
    let (projs : List (Option expr)) ←
      fields.mmap fun ⟨f, a⟩ => do
          let x_e := a.app x
          let t ← infer_type x_e
          let s ← infer_type t
          let expr.sort (level.succ u) ← pure s | pure (none : Option expr)
          let level.zero ← pure u |
            "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
          let j ← tactic.mk_app `json_serializable.to_json [x_e]
          pure (some (quote.1 ((%%ₓquote.1 f.toString, %%ₓj) : Stringₓ × json)))
    tactic.exact (projs (quote.1 (Stringₓ × json)) level.zero)
    -- the reverse direction
          get_local
          `j >>=
        tactic.clear
    let json_fields
      ←-- check fields are present
            fields.mmap
          fun ⟨f, e⟩ => do
          let t ← infer_type e
          let s ← infer_type t
          let expr.sort (level.succ u) ← pure s | pure (f, none)
          -- do nothing for prop fields
              refine
              (pquote.1 fun p => json_serializable.field_get p (%%ₓquote.1 f.toString) >>= _)
          tactic.applyc `prod.rec
          get_local `p >>= tactic.clear
          let jf ← tactic.intro (`field ++ f)
          pure (f, some jf)
    refine (pquote.1 fun p => json_serializable.field_terminator p >> _)
    get_local `p >>= tactic.clear
    let ctor ← of_json_helper struct_name e [] json_fields
    exact ctor

