/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Automation to construct `traversable` instances
-/
import Mathbin.Control.Traversable.Lemmas

namespace Tactic.Interactive

open Tactic List Monadₓ Functor

unsafe def with_prefix : Option Name → Name → Name
  | none, n => n
  | some p, n => p ++ n

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `t
/-- similar to `nested_traverse` but for `functor` -/
unsafe def nested_map (f v : expr) : expr → tactic expr
  | t => do
    let t ← instantiate_mvars t
    mcond (succeeds <| is_def_eq t v) (pure f)
        (if ¬v (t t.app_fn) then do
          let cl ← mk_app `` Functor [t]
          let _inst ← mk_instance cl
          let f' ← nested_map t
          mk_mapp `` Functor.map [t, _inst, none, none, f']
        else fail f! "type {t } is not a functor with respect to variable {v}")

/-- similar to `traverse_field` but for `functor` -/
unsafe def map_field (n : Name) (cl f α β e : expr) : tactic expr := do
  let t ← infer_type e >>= whnf
  if t = n then fail "recursive types not supported"
    else
      if expr.alpha_eqv α e then pure β
      else
        if α t then do
          let f' ← nested_map f α t
          pure <| f' e
        else is_def_eq t cl >> mk_app `` comp.mk [e] <|> pure e

/-- similar to `traverse_constructor` but for `functor` -/
unsafe def map_constructor (c n : Name) (f α β : expr) (args₀ : List expr) (args₁ : List (Bool × expr))
    (rec_call : List expr) : tactic expr := do
  let g ← target
  let (_, args') ←
    mmapAccuml
        (fun (x : List expr) (y : Bool × expr) =>
          if y.1 then pure (x.tail, x.head) else Prod.mk rec_call <$> map_field n g.app_fn f α β y.2)
        rec_call args₁
  let constr ← mk_const c
  let r := constr.mk_app (args₀ ++ args')
  return r

/-- derive the `map` definition of a `functor` -/
unsafe def mk_map (type : Name) := do
  let ls ← local_context
  let [α, β, f, x] ← tactic.intro_lst [`α, `β, `f, `x]
  let et ← infer_type x
  let xs ← tactic.induction x
  xs fun x : Name × List expr × List (Name × expr) => do
      let (c, args, _) := x
      let (args, rec_call) ← args fun e => (bnot ∘ β) <$> infer_type e
      let args₀ ←
        args fun a => do
            let b ← et <$> infer_type a
            pure (b, a)
      map_constructor c type f α β (ls ++ [β]) args₀ rec_call >>= tactic.exact

unsafe def mk_mapp_aux' : expr → expr → List expr → tactic expr
  | fn, expr.pi n bi d b, a :: as => do
    infer_type a >>= unify d
    let fn ← head_beta (fn a)
    let t ← whnf (b.instantiate_var a)
    mk_mapp_aux' fn t as
  | fn, _, _ => pure fn

unsafe def mk_mapp' (fn : expr) (args : List expr) : tactic expr := do
  let t ← infer_type fn >>= whnf
  mk_mapp_aux' fn t args

/-- derive the equations for a specific `map` definition -/
unsafe def derive_map_equations (pre : Option Name) (n : Name) (vs : List expr) (tgt : expr) : tactic Unit := do
  let e ← get_env
  ((e n).enumFrom 1).mmap' fun ⟨i, c⟩ => do
      mk_meta_var tgt >>= set_goals ∘ pure
      let vs ← intro_lst <| vs expr.local_pp_name
      let [α, β, f] ← tactic.intro_lst [`α, `β, `f] >>= mmap instantiate_mvars
      let c' ← mk_mapp c <| vs some ++ [α]
      let tgt' ← infer_type c' >>= pis vs
      mk_meta_var tgt' >>= set_goals ∘ pure
      let vs ← tactic.intro_lst <| vs expr.local_pp_name
      let vs' ← tactic.intros
      let c' ← mk_mapp c <| vs some ++ [α]
      let arg ← mk_mapp' c' vs'
      let n_map ← mk_const (mkStrName (with_prefix pre n) "map")
      let call_map := fun x => mk_mapp' n_map (vs ++ [α, β, f, x])
      let lhs ← call_map arg
      let args ←
        vs' fun a => do
            let t ← infer_type a
            pure ((expr.const_name (expr.get_app_fn t) = n : Bool), a)
      let rec_call := args fun ⟨b, e⟩ => guardₓ b >> pure e
      let rec_call ← rec_call call_map
      let rhs ← map_constructor c n f α β (vs ++ [β]) args rec_call
      Monadₓ.join <| unify <$> infer_type lhs <*> infer_type rhs
      let eqn ← mk_app `` Eq [lhs, rhs]
      let ws := eqn
      let eqn ← pis ws eqn
      let eqn ← instantiate_mvars eqn
      let (_, pr) ← solve_aux eqn (tactic.intros >> refine (pquote.1 rfl))
      let eqn_n := (mkStrName (mkStrName (mkStrName (with_prefix pre n) "map") "equations") "_eqn").append_after i
      let pr ← instantiate_mvars pr
      add_decl <| declaration.thm eqn_n eqn eqn (pure pr)
      return ()
  set_goals []
  return ()

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `d
unsafe def derive_functor (pre : Option Name) : tactic Unit := do
  let vs ← local_context
  let quote.1 (Functor (%%ₓf)) ← target
  let env ← get_env
  let n := f.get_app_fn.const_name
  let d ← get_decl n
  refine (pquote.1 { map := _.. })
  let tgt ← target
  extract_def (mkStrName (with_prefix pre n) "map") d <| mk_map n
  when (d d.is_trusted) <| do
      let tgt ← pis vs tgt
      derive_map_equations pre n vs tgt

/-- `seq_apply_constructor f [x,y,z]` synthesizes `f <*> x <*> y <*> z` -/
private unsafe def seq_apply_constructor : expr → List (Sum expr expr) → tactic (List (tactic expr) × expr)
  | e, Sum.inr x :: xs =>
    Prod.map (cons intro1) id <$> (to_expr (pquote.1 ((%%ₓe) <*> %%ₓx)) >>= flip seq_apply_constructor xs)
  | e, Sum.inl x :: xs => Prod.map (cons <| pure x) id <$> seq_apply_constructor e xs
  | e, [] => return ([], e)

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `t
/-- ``nested_traverse f α (list (array n (list α)))`` synthesizes the expression
`traverse (traverse (traverse f))`. `nested_traverse` assumes that `α` appears in
`(list (array n (list α)))` -/
unsafe def nested_traverse (f v : expr) : expr → tactic expr
  | t => do
    let t ← instantiate_mvars t
    mcond (succeeds <| is_def_eq t v) (pure f)
        (if ¬v (t t.app_fn) then do
          let cl ← mk_app `` Traversable [t]
          let _inst ← mk_instance cl
          let f' ← nested_traverse t
          mk_mapp `` Traversable.traverse [t, _inst, none, none, none, none, f']
        else fail f! "type {t } is not traversable with respect to variable {v}")

/-- For a sum type `inductive foo (α : Type) | foo1 : list α → ℕ → foo | ...`
``traverse_field `foo appl_inst f `α `(x : list α)`` synthesizes
`traverse f x` as part of traversing `foo1`. -/
unsafe def traverse_field (n : Name) (appl_inst cl f v e : expr) : tactic (Sum expr expr) := do
  let t ← infer_type e >>= whnf
  if t = n then fail "recursive types not supported"
    else
      if v t then do
        let f' ← nested_traverse f v t
        pure <| Sum.inr <| f' e
      else is_def_eq t cl >> Sum.inr <$> mk_app `` comp.mk [e] <|> pure (Sum.inl e)

/-- For a sum type `inductive foo (α : Type) | foo1 : list α → ℕ → foo | ...`
``traverse_constructor `foo1 `foo appl_inst f `α `β [`(x : list α), `(y : ℕ)]``
synthesizes `foo1 <$> traverse f x <*> pure y.` -/
unsafe def traverse_constructor (c n : Name) (appl_inst f α β : expr) (args₀ : List expr) (args₁ : List (Bool × expr))
    (rec_call : List expr) : tactic expr := do
  let g ← target
  let args' ← mmapₓ (traverse_field n appl_inst g.app_fn f α) args₀
  let (_, args') ←
    mmapAccuml
        (fun (x : List expr) (y : Bool × _) =>
          if y.1 then pure (x.tail, Sum.inr x.head) else Prod.mk x <$> traverse_field n appl_inst g.app_fn f α y.2)
        rec_call args₁
  let constr ← mk_const c
  let v ← mk_mvar
  let constr' ← to_expr (pquote.1 (@pure _ (%%ₓappl_inst).toHasPure _ (%%ₓv)))
  let (vars_intro, r) ← seq_apply_constructor constr' (args₀.map Sum.inl ++ args')
  let gs ← get_goals
  set_goals [v]
  let vs ← vars_intro.mmap id
  tactic.exact (constr vs)
  done
  set_goals gs
  return r

/-- derive the `traverse` definition of a `traversable` instance -/
unsafe def mk_traverse (type : Name) := do
  do
    let ls ← local_context
    let [m, appl_inst, α, β, f, x] ← tactic.intro_lst [`m, `appl_inst, `α, `β, `f, `x]
    let et ← infer_type x
    reset_instance_cache
    let xs ← tactic.induction x
    xs fun x : Name × List expr × List (Name × expr) => do
        let (c, args, _) := x
        let (args, rec_call) ← args fun e => (bnot ∘ β) <$> infer_type e
        let args₀ ←
          args fun a => do
              let b ← et <$> infer_type a
              pure (b, a)
        traverse_constructor c type appl_inst f α β (ls ++ [β]) args₀ rec_call >>= tactic.exact

open Applicativeₓ

/-- derive the equations for a specific `traverse` definition -/
unsafe def derive_traverse_equations (pre : Option Name) (n : Name) (vs : List expr) (tgt : expr) : tactic Unit := do
  let e ← get_env
  ((e n).enumFrom 1).mmap' fun ⟨i, c⟩ => do
      mk_meta_var tgt >>= set_goals ∘ pure
      let vs ← intro_lst <| vs expr.local_pp_name
      let [m, appl_inst, α, β, f] ← tactic.intro_lst [`m, `appl_inst, `α, `β, `f] >>= mmap instantiate_mvars
      let c' ← mk_mapp c <| vs some ++ [α]
      let tgt' ← infer_type c' >>= pis vs
      mk_meta_var tgt' >>= set_goals ∘ pure
      let vs ← tactic.intro_lst <| vs expr.local_pp_name
      let c' ← mk_mapp c <| vs some ++ [α]
      let vs' ← tactic.intros
      let arg ← mk_mapp' c' vs'
      let n_map ← mk_const (mkStrName (with_prefix pre n) "traverse")
      let call_traverse := fun x => mk_mapp' n_map (vs ++ [m, appl_inst, α, β, f, x])
      let lhs ← call_traverse arg
      let args ←
        vs' fun a => do
            let t ← infer_type a
            pure ((expr.const_name (expr.get_app_fn t) = n : Bool), a)
      let rec_call := args fun ⟨b, e⟩ => guardₓ b >> pure e
      let rec_call ← rec_call call_traverse
      let rhs ← traverse_constructor c n appl_inst f α β (vs ++ [β]) args rec_call
      Monadₓ.join <| unify <$> infer_type lhs <*> infer_type rhs
      let eqn ← mk_app `` Eq [lhs, rhs]
      let ws := eqn
      let eqn ← pis ws eqn
      let eqn ← instantiate_mvars eqn
      let (_, pr) ← solve_aux eqn (tactic.intros >> refine (pquote.1 rfl))
      let eqn_n := (mkStrName (mkStrName (mkStrName (with_prefix pre n) "traverse") "equations") "_eqn").append_after i
      let pr ← instantiate_mvars pr
      add_decl <| declaration.thm eqn_n eqn eqn (pure pr)
      return ()
  set_goals []
  return ()

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `d
unsafe def derive_traverse (pre : Option Name) : tactic Unit := do
  let vs ← local_context
  let quote.1 (Traversable (%%ₓf)) ← target
  let env ← get_env
  let n := f.get_app_fn.const_name
  let d ← get_decl n
  constructor
  let tgt ← target
  extract_def (mkStrName (with_prefix pre n) "traverse") d <| mk_traverse n
  when (d d.is_trusted) <| do
      let tgt ← pis vs tgt
      derive_traverse_equations pre n vs tgt

unsafe def mk_one_instance (n : Name) (cls : Name) (tac : tactic Unit) (namesp : Option Name)
    (mk_inst : Name → expr → tactic expr := fun n arg => mk_app n [arg]) : tactic Unit := do
  let decl ← get_decl n
  let cls_decl ← get_decl cls
  let env ← get_env
  guardₓ (env n) <|> fail f! "failed to derive '{cls }', '{n}' is not an inductive type"
  let ls := decl.univ_params.map fun n => level.param n
  let-- incrementally build up target expression `Π (hp : p) [cls hp] ..., cls (n.{ls} hp ...)`
  -- where `p ...` are the inductive parameter types of `n`
  tgt : expr := expr.const n ls
  let ⟨params, _⟩ ← open_pis (decl.type.instantiate_univ_params (decl.univ_params.zip ls))
  let params := params.init
  let tgt := tgt.mk_app params
  let tgt ← mk_inst cls tgt
  let tgt ←
    params.enum.mfoldr
        (fun ⟨i, param⟩ tgt => do
          let tgt ←
            (-- add typeclass hypothesis for each inductive parameter
                do
                  guardₓ <| i < env n
                  let param_cls ← mk_app cls [param]
                  pure <| expr.pi `a BinderInfo.inst_implicit param_cls tgt) <|>
                pure tgt
          pure <| tgt param)
        tgt
  () <$ mk_instance tgt <|> do
      let (_, val) ←
        tactic.solve_aux tgt do
            tactic.intros >> tac
      let val ← instantiate_mvars val
      let trusted := decl ∧ cls_decl
      let inst_n := with_prefix namesp n ++ cls
      add_decl (declaration.defn inst_n decl tgt val ReducibilityHints.abbrev trusted)
      set_basic_attribute `instance inst_n namesp

open Interactive

unsafe def get_equations_of (n : Name) : tactic (List pexpr) := do
  let e ← get_env
  let pre := mkStrName n "equations"
  let x := (e.fold []) fun d xs => if pre.isPrefixOf d.to_name then d.to_name :: xs else xs
  x resolve_name

unsafe def derive_lawful_functor (pre : Option Name) : tactic Unit := do
  let quote.1 (@IsLawfulFunctor (%%ₓf) (%%ₓd)) ← target
  refine (pquote.1 { .. })
  let n := f.get_app_fn.const_name
  let rules := fun r => [simp_arg_type.expr r, simp_arg_type.all_hyps]
  let goal := Loc.ns [none]
  solve1 do
      let vs ← tactic.intros
      try <| dunfold [`` Functor.map] (loc.ns [none])
      dunfold [mkStrName (with_prefix pre n) "map", `` id] (loc.ns [none])
      andthen (() <$ tactic.induction vs) (simp none none ff (rules (pquote.1 Functor.map_id)) [] goal)
  focus1 do
      let vs ← tactic.intros
      try <| dunfold [`` Functor.map] (loc.ns [none])
      dunfold [mkStrName (with_prefix pre n) "map", `` id] (loc.ns [none])
      andthen (() <$ tactic.induction vs) (simp none none ff (rules (pquote.1 Functor.map_comp_map)) [] goal)
  return ()

unsafe def simp_functor (rs : List simp_arg_type := []) : tactic Unit :=
  simp none none false rs [`functor_norm] (Loc.ns [none])

unsafe def traversable_law_starter (rs : List simp_arg_type) := do
  let vs ← tactic.intros
  resetI
  dunfold [`` Traversable.traverse, `` Functor.map] (loc.ns [none])
  andthen (() <$ tactic.induction vs) (simp_functor rs)

unsafe def derive_lawful_traversable (pre : Option Name) : tactic Unit := do
  let quote.1 (@IsLawfulTraversable (%%ₓf) (%%ₓd)) ← target
  let n := f.get_app_fn.const_name
  let eqns ← get_equations_of (mkStrName (with_prefix pre n) "traverse")
  let eqns' ← get_equations_of (mkStrName (with_prefix pre n) "map")
  let def_eqns := eqns.map simp_arg_type.expr ++ eqns'.map simp_arg_type.expr ++ [simp_arg_type.all_hyps]
  let comp_def := [simp_arg_type.expr (pquote.1 Function.comp)]
  let tr_map := List.map simp_arg_type.expr [pquote.1 Traversable.traverse_eq_map_id']
  let natur := fun η : expr => [simp_arg_type.expr (pquote.1 (Traversable.naturality_pf (%%ₓη)))]
  let goal := Loc.ns [none]
  andthen
      (andthen constructor
        [andthen (traversable_law_starter def_eqns) refl,
          andthen (traversable_law_starter def_eqns) (refl <|> simp_functor (def_eqns ++ comp_def)),
          andthen (traversable_law_starter def_eqns) (refl <|> simp none none tt tr_map [] goal),
          andthen (traversable_law_starter def_eqns)
            (refl <|> do
              let η ←
                get_local `η <|> do
                    let t ← mk_const `` IsLawfulTraversable.naturality >>= infer_type >>= pp
                    fail
                        f! "expecting an `applicative_transformation` called `η` in
                          naturality : {t}"
              simp none none tt (natur η) [] goal)])
      refl
  return ()

open Function

unsafe def guard_class (cls : Name) (hdl : derive_handler) : derive_handler := fun p n =>
  if p.is_constant_of cls then hdl p n else pure false

unsafe def higher_order_derive_handler (cls : Name) (tac : tactic Unit) (deps : List derive_handler := [])
    (namesp : Option Name) (mk_inst : Name → expr → tactic expr := fun n arg => mk_app n [arg]) : derive_handler :=
  fun p n => do
  mmap' (fun f : derive_handler => f p n) deps
  mk_one_instance n cls tac namesp mk_inst
  pure tt

unsafe def functor_derive_handler' (nspace : Option Name := none) : derive_handler :=
  higher_order_derive_handler `` Functor (derive_functor nspace) [] nspace

@[derive_handler]
unsafe def functor_derive_handler : derive_handler :=
  guard_class `` Functor functor_derive_handler'

unsafe def traversable_derive_handler' (nspace : Option Name := none) : derive_handler :=
  higher_order_derive_handler `` Traversable (derive_traverse nspace) [functor_derive_handler' nspace] nspace

@[derive_handler]
unsafe def traversable_derive_handler : derive_handler :=
  guard_class `` Traversable traversable_derive_handler'

unsafe def lawful_functor_derive_handler' (nspace : Option Name := none) : derive_handler :=
  higher_order_derive_handler `` IsLawfulFunctor (derive_lawful_functor nspace) [traversable_derive_handler' nspace]
    nspace fun n arg => mk_mapp n [arg, none]

@[derive_handler]
unsafe def lawful_functor_derive_handler : derive_handler :=
  guard_class `` IsLawfulFunctor lawful_functor_derive_handler'

unsafe def lawful_traversable_derive_handler' (nspace : Option Name := none) : derive_handler :=
  higher_order_derive_handler `` IsLawfulTraversable (derive_lawful_traversable nspace)
    [traversable_derive_handler' nspace, lawful_functor_derive_handler' nspace] nspace fun n arg =>
    mk_mapp n [arg, none]

@[derive_handler]
unsafe def lawful_traversable_derive_handler : derive_handler :=
  guard_class `` IsLawfulTraversable lawful_traversable_derive_handler'

end Tactic.Interactive

