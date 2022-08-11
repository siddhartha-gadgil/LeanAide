/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Scott Morrison, Keeley Hoek
-/
import Mathbin.Control.Basic
import Mathbin.Data.Dlist.Basic
import Mathbin.Meta.Expr
import Leanbin.System.Io
import Mathbin.Tactic.BinderMatching
import Mathbin.Tactic.InteractiveExpr
import Mathbin.Tactic.LeanCoreDocs
import Mathbin.Tactic.ProjectDir

universe u

deriving instance has_reflect, DecidableEq for Tactic.Transparency

-- Rather than import data.prod.lex here, we can get away with defining the order by hand.
instance : LT Pos where lt := fun x y => x.line < y.line ∨ x.line = y.line ∧ x.column < y.column

namespace Tactic

/-- Reflexivity conversion: given `e` returns `(e, ⊢ e = e)` -/
unsafe def refl_conv (e : expr) : tactic (expr × expr) := do
  let p ← mk_eq_refl e
  return (e, p)

/-- Turns a conversion tactic into one that always succeeds, where failure is interpreted as a
proof by reflexivity. -/
unsafe def or_refl_conv (tac : expr → tactic (expr × expr)) (e : expr) : tactic (expr × expr) :=
  tac e <|> refl_conv e

/-- Transitivity conversion: given two conversions (which take an
expression `e` and returns `(e', ⊢ e = e')`), produces another
conversion that combines them with transitivity, treating failures
as reflexivity conversions. -/
unsafe def trans_conv (t₁ t₂ : expr → tactic (expr × expr)) (e : expr) : tactic (expr × expr) :=
  (do
      let (e₁, p₁) ← t₁ e
      (do
            let (e₂, p₂) ← t₂ e₁
            let p ← mk_eq_trans p₁ p₂
            return (e₂, p)) <|>
          return (e₁, p₁)) <|>
    t₂ e

end Tactic

open Tactic

namespace Expr

/-- Given an expr `α` representing a type with numeral structure,
`of_nat α n` creates the `α`-valued numeral expression corresponding to `n`. -/
protected unsafe def of_nat (α : expr) : ℕ → tactic expr :=
  Nat.binaryRec (tactic.mk_mapp `` Zero.zero [some α, none]) fun b n tac =>
    if n = 0 then mk_mapp `` One.one [some α, none]
    else do
      let e ← tac
      tactic.mk_app (cond b `` bit1 `` bit0) [e]

/-- Given an expr `α` representing a type with numeral structure,
`of_int α n` creates the `α`-valued numeral expression corresponding to `n`.
The output is either a numeral or the negation of a numeral. -/
protected unsafe def of_int (α : expr) : ℤ → tactic expr
  | (n : ℕ) => expr.of_nat α n
  | -[1+ n] => do
    let e ← expr.of_nat α (n + 1)
    tactic.mk_app `` Neg.neg [e]

/-- Convert a list of expressions to an expression denoting the list of those expressions. -/
unsafe def of_list (α : expr) : List expr → tactic expr
  | [] => tactic.mk_app `` List.nil [α]
  | x :: xs => do
    let exs ← of_list xs
    tactic.mk_app `` List.cons [α, x, exs]

/-- Generates an expression of the form `∃(args), inner`. `args` is assumed to be a list of local
constants. When possible, `p ∧ q` is used instead of `∃(_ : p), q`. -/
unsafe def mk_exists_lst (args : List expr) (inner : expr) : tactic expr :=
  args.mfoldr
    (fun arg i : expr => do
      let t ← infer_type arg
      let sort l ← infer_type t
      return <| if arg i ∨ l ≠ level.zero then (const `Exists [l] : expr) t (i [arg]) else (const `and [] : expr) t i)
    inner

/-- `traverse f e` applies the monadic function `f` to the direct descendants of `e`. -/
unsafe def traverse {m : Type → Type u} [Applicativeₓ m] {elab elab' : Bool} (f : expr elab → m (expr elab')) :
    expr elab → m (expr elab')
  | var v => pure <| var v
  | sort l => pure <| sort l
  | const n ls => pure <| const n ls
  | mvar n n' e => mvar n n' <$> f e
  | local_const n n' bi e => local_const n n' bi <$> f e
  | app e₀ e₁ => app <$> f e₀ <*> f e₁
  | lam n bi e₀ e₁ => lam n bi <$> f e₀ <*> f e₁
  | pi n bi e₀ e₁ => pi n bi <$> f e₀ <*> f e₁
  | elet n e₀ e₁ e₂ => elet n <$> f e₀ <*> f e₁ <*> f e₂
  | macro mac es => macro mac <$> List.traverseₓₓ f es

/-- `mfoldl f a e` folds the monadic function `f` over the subterms of the expression `e`,
with initial value `a`. -/
unsafe def mfoldl {α : Type} {m} [Monadₓ m] (f : α → expr → m α) : α → expr → m α
  | x, e => Prod.snd <$> (StateTₓ.run (e.traverse fun e' => (get >>= monad_lift ∘ flip f e' >>= put) $> e') x : m _)

/-- `kreplace e old new` replaces all occurrences of the expression `old` in `e`
with `new`. The occurrences of `old` in `e` are determined using keyed matching
with transparency `md`; see `kabstract` for details. If `unify` is true,
we may assign metavariables in `e` as we match subterms of `e` against `old`. -/
unsafe def kreplace (e old new : expr) (md := semireducible) (unify := true) : tactic expr := do
  let e ← kabstract e old md unify
  pure <| e new

end Expr

namespace Name

/-- `pre.contains_sorry_aux nm` checks whether `sorry` occurs in the value of the declaration `nm`
or (recusively) in any declarations occurring in the value of `nm` with namespace `pre`.
Auxiliary function for `name.contains_sorry`. -/
unsafe def contains_sorry_aux (pre : Name) : Name → tactic Bool
  | nm => do
    let env ← get_env
    let decl ← get_decl nm
    let ff ← return decl.value.contains_sorry | return true
    ((decl pre).mfold ff) fun n b => if b then return tt else n

/-- `nm.contains_sorry` checks whether `sorry` occurs in the value of the declaration `nm` or
  in any declarations `nm._proof_i` (or to be more precise: any declaration in namespace `nm`).
  See also `expr.contains_sorry`. -/
unsafe def contains_sorry (nm : Name) : tactic Bool :=
  nm.contains_sorry_aux nm

end Name

namespace InteractionMonad

open Result

variable {σ : Type} {α : Type u}

/-- `get_state` returns the underlying state inside an interaction monad, from within that monad. -/
-- Note that this is a generalization of `tactic.read` in core.
unsafe def get_state : interaction_monad σ σ := fun state => success State State

/-- `set_state` sets the underlying state inside an interaction monad, from within that monad. -/
-- Note that this is a generalization of `tactic.write` in core.
unsafe def set_state (state : σ) : interaction_monad σ Unit := fun _ => success () State

/-- `run_with_state state tac` applies `tac` to the given state `state` and returns the result,
subsequently restoring the original state.
If `tac` fails, then `run_with_state` does too.
-/
unsafe def run_with_state (state : σ) (tac : interaction_monad σ α) : interaction_monad σ α := fun s =>
  match tac State with
  | success val _ => success val s
  | exception fn Pos _ => exception fn Pos s

end InteractionMonad

namespace Format

/-- `join' [a,b,c]` produces the format object `abc`.
It differs from `format.join` by using `format.nil` instead of `""` for the empty list. -/
unsafe def join' (xs : List format) : format :=
  xs.foldl compose nil

/-- `intercalate x [a, b, c]` produces the format object `a.x.b.x.c`,
where `.` represents `format.join`. -/
unsafe def intercalate (x : format) : List format → format :=
  join' ∘ List.intersperse x

/-- `soft_break` is similar to `line`. Whereas in `group (x ++ line ++ y ++ line ++ z)`
the result either fits on one line or in three, `x ++ soft_break ++ y ++ soft_break ++ z`
each line break is decided independently -/
unsafe def soft_break : format :=
  group line

/-- Format a list as a comma separated list, without any brackets. -/
unsafe def comma_separated {α : Type _} [has_to_format α] : List α → format
  | [] => nil
  | xs => group (nest 1 <| intercalate ("," ++ soft_break) <| xs.map to_fmt)

end Format

section Format

open Format

/-- format a `list` by separating elements with `soft_break` instead of `line` -/
unsafe def list.to_line_wrap_format {α : Type u} [has_to_format α] (l : List α) : format :=
  bracket "[" "]" (comma_separated l)

end Format

namespace Tactic

open Function

export InteractionMonad (get_state set_state run_with_state)

/-- Private work function for `add_local_consts_as_local_hyps`: given
    `mappings : list (expr × expr)` corresponding to pairs `(var, hyp)` of variables and the local
    hypothesis created as a result and `(var :: rest) : list expr` of more local variables we
    examine `var` to see if it contains any other variables in `rest`. If it does, we put it to the
    back of the queue and recurse. If it does not, then we perform replacements inside the type of
    `var` using the `mappings`, create a new associate local hypothesis, add this to the list of
    mappings, and recurse. We are done once all local hypotheses have been processed.

    If the list of passed local constants have types which depend on one another (which can only
    happen by hand-crafting the `expr`s manually), this function will loop forever. -/
private unsafe def add_local_consts_as_local_hyps_aux : List (expr × expr) → List expr → tactic (List (expr × expr))
  | mappings, [] => return mappings
  | mappings, var :: rest => do
    let-- Determine if `var` contains any local variables in the lift `rest`.
    is_dependent := (var.local_type.fold false) fun e n b => if b then b else e ∈ rest
    -- If so, then skip it---add it to the end of the variable queue.
        if is_dependent then add_local_consts_as_local_hyps_aux mappings (rest ++ [var])
      else do
        let/- Otherwise, replace all of the local constants referenced by the type of `var` with the
               respective new corresponding local hypotheses as recorded in the list `mappings`. -/
        new_type := var mappings
        let hyp
          ←-- Introduce a new local new local hypothesis `hyp` for `var`, with the correct type.
              assertv
              var new_type (var new_type)
        /- Process the next variable in the queue, with the mapping list updated to include the local
                   hypothesis which we just created. -/
            add_local_consts_as_local_hyps_aux
            ((var, hyp) :: mappings) rest

/-- `add_local_consts_as_local_hyps vars` add the given list `vars` of `expr.local_const`s to the
    tactic state. This is harder than it sounds, since the list of local constants which we have
    been passed can have dependencies between their types.

    For example, suppose we have two local constants `n : ℕ` and `h : n = 3`. Then we cannot blindly
    add `h` as a local hypothesis, since we need the `n` to which it refers to be the `n` created as
    a new local hypothesis, not the old local constant `n` with the same name. Of course, these
    dependencies can be nested arbitrarily deep.

    If the list of passed local constants have types which depend on one another (which can only
    happen by hand-crafting the `expr`s manually), this function will loop forever. -/
unsafe def add_local_consts_as_local_hyps (vars : List expr) : tactic (List (expr × expr)) :=
  /- The `list.reverse` below is a performance optimisation since the list of available variables
       reported by the system is often mostly the reverse of the order in which they are dependent. -/
    add_local_consts_as_local_hyps_aux
    [] vars.reverse.dedup

private unsafe def get_expl_pi_arity_aux : expr → tactic Nat
  | expr.pi n bi d b => do
    let m ← mk_fresh_name
    let l := expr.local_const m n bi d
    let new_b ← whnf (expr.instantiate_var b l)
    let r ← get_expl_pi_arity_aux new_b
    if bi = BinderInfo.default then return (r + 1) else return r
  | e => return 0

/-- Compute the arity of explicit arguments of `type`. -/
unsafe def get_expl_pi_arity (type : expr) : tactic Nat :=
  whnf type >>= get_expl_pi_arity_aux

/-- Compute the arity of explicit arguments of `fn`'s type. -/
unsafe def get_expl_arity (fn : expr) : tactic Nat :=
  infer_type fn >>= get_expl_pi_arity

private unsafe def get_app_fn_args_whnf_aux (md : Transparency) (unfold_ginductive : Bool) :
    List expr → expr → tactic (expr × List expr) := fun args e => do
  let e ← whnf e md unfold_ginductive
  match e with
    | expr.app t u => get_app_fn_args_whnf_aux (u :: args) t
    | _ => pure (e, args)

/-- For `e = f x₁ ... xₙ`, `get_app_fn_args_whnf e` returns `(f, [x₁, ..., xₙ])`. `e`
is normalised as necessary; for example:

```
get_app_fn_args_whnf `(let f := g x in f y) = (`(g), [`(x), `(y)])
```

The returned expression is in whnf, but the arguments are generally not.
-/
unsafe def get_app_fn_args_whnf (e : expr) (md := semireducible) (unfold_ginductive := true) :
    tactic (expr × List expr) :=
  get_app_fn_args_whnf_aux md unfold_ginductive [] e

/-- `get_app_fn_whnf e md unfold_ginductive` is like `expr.get_app_fn e` but `e` is
normalised as necessary (with transparency `md`). `unfold_ginductive` controls
whether constructors of generalised inductive types are unfolded. The returned
expression is in whnf.
-/
unsafe def get_app_fn_whnf : expr → optParam _ semireducible → optParam _ true → tactic expr
  | e, md, unfold_ginductive => do
    let e ← whnf e md unfold_ginductive
    match e with
      | expr.app f _ => get_app_fn_whnf f md unfold_ginductive
      | _ => pure e

/-- `get_app_fn_const_whnf e md unfold_ginductive` expects that `e = C x₁ ... xₙ`,
where `C` is a constant, after normalisation with transparency `md`. If so, the
name of `C` is returned. Otherwise the tactic fails. `unfold_ginductive`
controls whether constructors of generalised inductive types are unfolded.
-/
unsafe def get_app_fn_const_whnf (e : expr) (md := semireducible) (unfold_ginductive := true) : tactic Name := do
  let f ← get_app_fn_whnf e md unfold_ginductive
  match f with
    | expr.const n _ => pure n
    | _ =>
      fail
        f! "expected a constant (possibly applied to some arguments), but got:
          {e}"

/-- `get_app_args_whnf e md unfold_ginductive` is like `expr.get_app_args e` but `e`
is normalised as necessary (with transparency `md`). `unfold_ginductive`
controls whether constructors of generalised inductive types are unfolded. The
returned expressions are not necessarily in whnf.
-/
unsafe def get_app_args_whnf (e : expr) (md := semireducible) (unfold_ginductive := true) : tactic (List expr) :=
  Prod.snd <$> get_app_fn_args_whnf e md unfold_ginductive

/-- `pis loc_consts f` is used to create a pi expression whose body is `f`.
`loc_consts` should be a list of local constants. The function will abstract these local
constants from `f` and bind them with pi binders.

For example, if `a, b` are local constants with types `Ta, Tb`,
``pis [a, b] `(f a b)`` will return the expression
`Π (a : Ta) (b : Tb), f a b`. -/
unsafe def pis : List expr → expr → tactic expr
  | e@(expr.local_const uniq pp info _) :: es, f => do
    let t ← infer_type e
    let f' ← pis es f
    pure <| expr.pi pp info t (expr.abstract_local f' uniq)
  | _, f => pure f

/-- `lambdas loc_consts f` is used to create a lambda expression whose body is `f`.
`loc_consts` should be a list of local constants. The function will abstract these local
constants from `f` and bind them with lambda binders.

For example, if `a, b` are local constants with types `Ta, Tb`,
``lambdas [a, b] `(f a b)`` will return the expression
`λ (a : Ta) (b : Tb), f a b`. -/
unsafe def lambdas : List expr → expr → tactic expr
  | e@(expr.local_const uniq pp info _) :: es, f => do
    let t ← infer_type e
    let f' ← lambdas es f
    pure <| expr.lam pp info t (expr.abstract_local f' uniq)
  | _, f => pure f

/-- Given an expression `f` (likely a binary operation) and a further expression `x`, calling
`list_binary_operands f x` breaks `x` apart into successions of applications of `f` until this can
no longer be done and returns a list of the leaves of the process.

This matches `f` up to semireducible unification. In particular, it will match applications of the
same polymorphic function with different type-class arguments.

E.g., if `i1` and `i2` are both instances of `has_add T` and
`e := has_add.add T i1 x (has_add.add T i2 y z)`, then ``list_binary_operands `((+) : T → T → T) e``
returns `[x, y, z]`.

For example:
```lean
#eval list_binary_operands `(@has_add.add ℕ _) `(3 + (4 * 5 + 6) + 7 / 3) >>= tactic.trace
-- [3, 4 * 5, 6, 7 / 3]
#eval list_binary_operands `(@list.append ℕ) `([1, 2] ++ [3, 4] ++ (1 :: [])) >>= tactic.trace
-- [[1, 2], [3, 4], [1]]
```
-/
unsafe def list_binary_operands (f : expr) : expr → tactic (List expr)
  | x@(expr.app (expr.app g a) b) => do
    let some _ ← try_core (unify f g) | pure [x]
    let as ← list_binary_operands a
    let bs ← list_binary_operands b
    pure (as ++ bs)
  | a => pure [a]

/-- `mk_theorem n ls t e` creates a theorem declaration with name `n`, universe parameters named
`ls`, type `t`, and body `e`. -/
-- TODO: move to `declaration` namespace in `meta/expr.lean`
unsafe def mk_theorem (n : Name) (ls : List Name) (t : expr) (e : expr) : declaration :=
  declaration.thm n ls t (task.pure e)

/-- `add_theorem_by n ls type tac` uses `tac` to synthesize a term with type `type`, and adds this
to the environment as a theorem with name `n` and universe parameters `ls`. -/
unsafe def add_theorem_by (n : Name) (ls : List Name) (type : expr) (tac : tactic Unit) : tactic expr := do
  let ((), body) ← solve_aux type tac
  let body ← instantiate_mvars body
  add_decl <| mk_theorem n ls type body
  return <| expr.const n <| ls level.param

/-- `eval_expr' α e` attempts to evaluate the expression `e` in the type `α`.
This is a variant of `eval_expr` in core. Due to unexplained behavior in the VM, in rare
situations the latter will fail but the former will succeed. -/
unsafe def eval_expr' (α : Type _) [_inst_1 : reflected _ α] (e : expr) : tactic α :=
  mk_app `` id [e] >>= eval_expr α

/-- `mk_fresh_name` returns identifiers starting with underscores,
which are not legal when emitted by tactic programs. `mk_user_fresh_name`
turns the useful source of random names provided by `mk_fresh_name` into
names which are usable by tactic programs.

The returned name has four components which are all strings. -/
unsafe def mk_user_fresh_name : tactic Name := do
  let nm ← mk_fresh_name
  return <| `user__ ++ nm ++ `user__

/-- `has_attribute' attr_name decl_name` checks
whether `decl_name` exists and has attribute `attr_name`. -/
unsafe def has_attribute' (attr_name decl_name : Name) : tactic Bool :=
  succeeds (has_attribute attr_name decl_name)

/-- Checks whether the name is a simp lemma -/
unsafe def is_simp_lemma : Name → tactic Bool :=
  has_attribute' `simp

/-- Checks whether the name is an instance. -/
unsafe def is_instance : Name → tactic Bool :=
  has_attribute' `instance

/-- `local_decls` returns a dictionary mapping names to their corresponding declarations.
Covers all declarations from the current file. -/
unsafe def local_decls : tactic (name_map declaration) := do
  let e ← tactic.get_env
  let xs :=
    e.fold native.mk_rb_map fun d s => if environment.in_current_file e d.to_name then s.insert d.to_name d else s
  pure xs

/-- `get_decls_from` returns a dictionary mapping names to their
corresponding declarations.  Covers all declarations the files listed
in `fs`, with the current file listed as `none`.

The path of the file names is expected to be relative to
the root of the project (i.e. the location of `leanpkg.toml` when it
is present); e.g. `"src/tactic/core.lean"`

Possible issue: `get_decls_from` uses `get_cwd`, the current working
directory, which may not always point at the root of the project.
It would work better if it searched for the root directory or,
better yet, if Lean exposed its path information.
-/
unsafe def get_decls_from (fs : List (Option Stringₓ)) : tactic (name_map declaration) := do
  let root ← unsafe_run_io <| Io.Env.getCwd
  let fs := fs.map (Option.map fun path => root ++ "/" ++ path)
  let err ← unsafe_run_io <| (fs.filterMap id).mfilter <| (· <$> ·) bnot ∘ Io.Fs.fileExists
  guardₓ (err = []) <|> fail f! "File not found: {err}"
  let e ← tactic.get_env
  let xs :=
    e.fold native.mk_rb_map fun d s =>
      let source := e.decl_olean d.to_name
      if source ∈ fs ∧ (source = none → e.in_current_file d.to_name) then s.insert d.to_name d else s
  pure xs

/-- If `{nm}_{n}` doesn't exist in the environment, returns that, otherwise tries `{nm}_{n+1}` -/
unsafe def get_unused_decl_name_aux (e : environment) (nm : Name) : ℕ → tactic Name
  | n =>
    let nm' := nm.appendSuffix ("_" ++ toString n)
    if e.contains nm' then get_unused_decl_name_aux (n + 1) else return nm'

/-- Return a name which doesn't already exist in the environment. If `nm` doesn't exist, it
returns that, otherwise it tries `nm_2`, `nm_3`, ... -/
unsafe def get_unused_decl_name (nm : Name) : tactic Name :=
  get_env >>= fun e => if e.contains nm then get_unused_decl_name_aux e nm 2 else return nm

/-- Returns a pair `(e, t)`, where `e ← mk_const d.to_name`, and `t = d.type`
but with universe params updated to match the fresh universe metavariables in `e`.

This should have the same effect as just
```lean
do e ← mk_const d.to_name,
   t ← infer_type e,
   return (e, t)
```
but is hopefully faster.
-/
unsafe def decl_mk_const (d : declaration) : tactic (expr × expr) := do
  let subst ← d.univ_params.mmap fun u => Prod.mk u <$> mk_meta_univ
  let e : expr := expr.const d.to_name (Prod.snd <$> subst)
  return (e, d subst)

/-- Replace every universe metavariable in an expression with a universe parameter.

(This is useful when making new declarations.)
-/
unsafe def replace_univ_metas_with_univ_params (e : expr) : tactic expr := do
  e fun n => do
      let n' := `u.appendSuffix ("_" ++ toString (n.1 + 1))
      unify (expr.sort (level.mvar n.2)) (expr.sort (level.param n'))
  instantiate_mvars e

/-- `mk_local n` creates a dummy local variable with name `n`.
The type of this local constant is a constant with name `n`, so it is very unlikely to be
a meaningful expression. -/
unsafe def mk_local (n : Name) : expr :=
  expr.local_const n n BinderInfo.default (expr.const n [])

/-- `mk_psigma [x,y,z]`, with `[x,y,z]` list of local constants of types `x : tx`,
`y : ty x` and `z : tz x y`, creates an expression of sigma type:
`⟨x,y,z⟩ : Σ' (x : tx) (y : ty x), tz x y`.
-/
unsafe def mk_psigma : List expr → tactic expr
  | [] => mk_const `` PUnit
  | [x@(expr.local_const _ _ _ _)] => pure x
  | x@(expr.local_const _ _ _ _) :: xs => do
    let y ← mk_psigma xs
    let α ← infer_type x
    let β ← infer_type y
    let t ← lambdas [x] β >>= instantiate_mvars
    let r ← mk_mapp `` PSigma.mk [α, t]
    pure <| r x y
  | _ => fail "mk_psigma expects a list of local constants"

/-- Update the type of a local constant or metavariable. For local constants and
metavariables obtained via, for example, `tactic.get_local`, the type stored in
the expression is not necessarily the same as the type returned by `infer_type`.
This tactic, given a local constant or metavariable, updates the stored type to
match the output of `infer_type`. If the input is not a local constant or
metavariable, `update_type` does nothing.
-/
unsafe def update_type : expr → tactic expr
  | e@(expr.local_const ppname uname binfo _) => expr.local_const ppname uname binfo <$> infer_type e
  | e@(expr.mvar ppname uname _) => expr.mvar ppname uname <$> infer_type e
  | e => pure e

/-- `elim_gen_prod n e _ ns` with `e` an expression of type `psigma _`, applies `cases` on `e` `n`
times and uses `ns` to name the resulting variables. Returns a triple: list of new variables,
remaining term and unused variable names.
-/
unsafe def elim_gen_prod : Nat → expr → List expr → List Name → tactic (List expr × expr × List Name)
  | 0, e, hs, ns => return (hs.reverse, e, ns)
  | n + 1, e, hs, ns => do
    let t ← infer_type e
    if t `eq then return (hs, e, ns)
      else do
        let [(_, [h, h'], _)] ← cases_core e (ns 1)
        elim_gen_prod n h' (h :: hs) (ns 1)

private unsafe def elim_gen_sum_aux : Nat → expr → List expr → tactic (List expr × expr)
  | 0, e, hs => return (hs, e)
  | n + 1, e, hs => do
    let [(_, [h], _), (_, [h'], _)] ← induction e []
    swap
    elim_gen_sum_aux n h' (h :: hs)

/-- `elim_gen_sum n e` applies cases on `e` `n` times. `e` is assumed to be a local constant whose
type is a (nested) sum `⊕`. Returns the list of local constants representing the components of `e`.
-/
unsafe def elim_gen_sum (n : Nat) (e : expr) : tactic (List expr) := do
  let (hs, h') ← elim_gen_sum_aux n e []
  let gs ← get_goals
  set_goals <| (gs (n + 1)).reverse ++ gs (n + 1)
  return <| hs ++ [h']

/-- Given `elab_def`, a tactic to solve the current goal,
`extract_def n trusted elab_def` will create an auxiliary definition named `n` and use it
to close the goal. If `trusted` is false, it will be a meta definition. -/
unsafe def extract_def (n : Name) (trusted : Bool) (elab_def : tactic Unit) : tactic Unit := do
  let cxt ← List.map expr.to_implicit_local_const <$> local_context
  let t ← target
  let (eqns, d) ← solve_aux t elab_def
  let d ← instantiate_mvars d
  let t' ← pis cxt t
  let d' ← lambdas cxt d
  let univ := t'.collect_univ_params
  add_decl <| declaration.defn n univ t' d' (ReducibilityHints.regular 1 tt) trusted
  applyc n

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- Attempts to close the goal with `dec_trivial`. -/
unsafe def exact_dec_trivial : tactic Unit :=
  sorry

/-- Runs a tactic for a result, reverting the state after completion. -/
unsafe def retrieve {α} (tac : tactic α) : tactic α := fun s =>
  result.cases_on (tac s) (fun a s' => result.success a s) result.exception

/-- Runs a tactic for a result, reverting the state after completion or error. -/
unsafe def retrieve' {α} (tac : tactic α) : tactic α := fun s =>
  result.cases_on (tac s) (fun a s' => result.success a s) fun msg pos s' => result.exception msg Pos s

/-- Repeat a tactic at least once, calling it recursively on all subgoals,
until it fails. This tactic fails if the first invocation fails. -/
unsafe def repeat1 (t : tactic Unit) : tactic Unit :=
  andthen t (repeat t)

/-- `iterate_range m n t`: Repeat the given tactic at least `m` times and
at most `n` times or until `t` fails. Fails if `t` does not run at least `m` times. -/
unsafe def iterate_range : ℕ → ℕ → tactic Unit → tactic Unit
  | 0, 0, t => skip
  | 0, n + 1, t => try (t >> iterate_range 0 n t)
  | m + 1, n, t => t >> iterate_range m (n - 1) t

/-- Given a tactic `tac` that takes an expression
and returns a new expression and a proof of equality,
use that tactic to change the type of the hypotheses listed in `hs`,
as well as the goal if `tgt = tt`.

Returns `tt` if any types were successfully changed.
-/
unsafe def replace_at (tac : expr → tactic (expr × expr)) (hs : List expr) (tgt : Bool) : tactic Bool := do
  let to_remove ←
    hs.mfilter fun h => do
        let h_type ← infer_type h
        succeeds <| do
            let (new_h_type, pr) ← tac h_type
            assert h new_h_type
            mk_eq_mp pr h >>= tactic.exact
  let goal_simplified ←
    succeeds <| do
        guardₓ tgt
        let (new_t, pr) ← target >>= tac
        replace_target new_t pr
  to_remove fun h => try (clear h)
  return (¬to_remove ∨ goal_simplified)

/-- `revert_after e` reverts all local constants after local constant `e`. -/
unsafe def revert_after (e : expr) : tactic ℕ := do
  let l ← local_context
  let [Pos] ← return <| l.indexesOf e | pp e >>= fun s => fail f! "No such local constant {s}"
  let l := l.drop Pos.succ
  -- all local hypotheses after `e`
      revert_lst
      l

/-- `revert_target_deps` reverts all local constants on which the target depends (recursively).
  Returns the number of local constants that have been reverted. -/
unsafe def revert_target_deps : tactic ℕ := do
  let tgt ← target
  let ctx ← local_context
  let l ← ctx.mfilter (kdepends_on tgt)
  let n ← revert_lst l
  if l = [] then return n
    else do
      let m ← revert_target_deps
      return (m + n)

/-- `generalize' e n` generalizes the target with respect to `e`. It creates a new local constant
with name `n` of the same type as `e` and replaces all occurrences of `e` by `n`.

`generalize'` is similar to `generalize` but also succeeds when `e` does not occur in the
goal, in which case it just calls `assert`.
In contrast to `generalize` it already introduces the generalized variable. -/
unsafe def generalize' (e : expr) (n : Name) : tactic expr :=
  generalize e n >> intro n <|> note n none e

/-- `intron_no_renames n` calls `intro` `n` times, using the pretty-printing name
provided by the binder to name the new local constant.
Unlike `intron`, it does not rename introduced constants if the names shadow existing constants.
-/
unsafe def intron_no_renames : ℕ → tactic Unit
  | 0 => pure ()
  | n + 1 => do
    let expr.pi pp_n _ _ _ ← target
    intro pp_n
    intron_no_renames n

/-- `get_univ_level t` returns the universe level of a type `t` -/
unsafe def get_univ_level (t : expr) (md := semireducible) (unfold_ginductive := true) : tactic level := do
  let expr.sort u ← infer_type t >>= fun s => whnf s md unfold_ginductive |
    fail "get_univ_level: argument is not a type"
  return u

/-!
### Various tactics related to local definitions (local constants of the form `x : α := t`)

We call `t` the value of `x`.
-/


/-- `local_def_value e` returns the value of the expression `e`, assuming that `e` has been defined
  locally using a `let` expression. Otherwise it fails. -/
unsafe def local_def_value (e : expr) : tactic expr :=
  pp e >>= fun s =>
    -- running `pp` here, because we cannot access it in the `type_context` monad.
      tactic.unsafe.type_context.run <|
      do
      let lctx ← tactic.unsafe.type_context.get_local_context
      let some ldecl ← return <| lctx.get_local_decl e.local_uniq_name |
        tactic.unsafe.type_context.fail f! "No such hypothesis {s}."
      let some let_val ← return ldecl.value |
        tactic.unsafe.type_context.fail f! "Variable {e} is not a local definition."
      return let_val

/-- `is_local_def e` succeeds when `e` is a local definition (a local constant of the form
`e : α := t`) and otherwise fails. -/
unsafe def is_local_def (e : expr) : tactic Unit := do
  let ctx ← unsafe.type_context.get_local_context.run
  let some decl ← pure <| ctx.get_local_decl e.local_uniq_name | fail f! "is_local_def: {e} is not a local constant"
  when decl <| fail f! "is_local_def: {e} is not a local definition"

/-- Returns the local definitions from the context. A local definition is a
local constant of the form `e : α := t`. The local definitions are returned in
the order in which they appear in the context. -/
unsafe def local_defs : tactic (List expr) := do
  let ctx ← unsafe.type_context.get_local_context.run
  let ctx' ← local_context
  ctx' fun h => do
      let some decl ← pure <| ctx h | fail f! "local_defs: local {h} not found in the local context"
      pure decl

/-- like `split_on_p p xs`, `partition_local_deps_aux vs xs acc` searches for matches in `xs`
(using membership to `vs` instead of a predicate) and breaks `xs` when matches are found.
whereas `split_on_p p xs` removes the matches, `partition_local_deps_aux vs xs acc` includes
them in the following partition. Also, `partition_local_deps_aux vs xs acc` discards the partition
running up to the first match. -/
private def partition_local_deps_aux {α} [DecidableEq α] (vs : List α) : List α → List α → List (List α)
  | [], Acc => [Acc.reverse]
  | l :: ls, Acc =>
    if l ∈ vs then Acc.reverse :: partition_local_deps_aux ls [l] else partition_local_deps_aux ls (l :: Acc)

/-- `partition_local_deps vs`, with `vs` a list of local constants,
reorders `vs` in the order they appear in the local context together
with the variables that follow them. If local context is `[a,b,c,d,e,f]`,
and that we call `partition_local_deps [d,b]`, we get `[[d,e,f], [b,c]]`.
The head of each list is one of the variables given as a parameter. -/
unsafe def partition_local_deps (vs : List expr) : tactic (List (List expr)) := do
  let ls ← local_context
  pure (partition_local_deps_aux vs ls []).tail.reverse

/-- `clear_value [e₀, e₁, e₂, ...]` clears the body of the local definitions `e₀`, `e₁`, `e₂`, ...
changing them into regular hypotheses. A hypothesis `e : α := t` is changed to `e : α`. The order of
locals `e₀`, `e₁`, `e₂` does not matter as a permutation will be chosen so as to preserve type
correctness. This tactic is called `clearbody` in Coq. -/
unsafe def clear_value (vs : List expr) : tactic Unit := do
  let ls ← partition_local_deps vs
  ls fun vs => do
      revert_lst vs
      let expr.elet v t d b ← target | fail f! "Cannot clear the body of {vs}. It is not a local definition."
      let e := expr.pi v BinderInfo.default t b
      type_check e <|> fail f! "Cannot clear the body of {vs}. The resulting goal is not type correct."
      let g ← mk_meta_var e
      let h ← note `h none g
      tactic.exact <| h d
      let gs ← get_goals
      set_goals <| g :: gs
  ls fun vs => intro_lst <| vs expr.local_pp_name

/-- `context_has_local_def` is true iff there is at least one local definition in
the context.
-/
unsafe def context_has_local_def : tactic Bool := do
  let ctx ← local_context
  ctx (succeeds ∘ local_def_value)

/-- `context_upto_hyp_has_local_def h` is true iff any of the hypotheses in the
context up to and including `h` is a local definition.
-/
unsafe def context_upto_hyp_has_local_def (h : expr) : tactic Bool := do
  let ff ← succeeds (local_def_value h) | pure true
  let ctx ← local_context
  let ctx := ctx.takeWhile (· ≠ h)
  ctx (succeeds ∘ local_def_value)

/-- If the expression `h` is a local variable with type `x = t` or `t = x`, where `x` is a local
constant, `tactic.subst' h` substitutes `x` by `t` everywhere in the main goal and then clears `h`.
If `h` is another local variable, then we find a local constant with type `h = t` or `t = h` and
substitute `t` for `h`.

This is like `tactic.subst`, but fails with a nicer error message if the substituted variable is a
local definition. It is trickier to fix this in core, since `tactic.is_local_def` is in mathlib.
-/
unsafe def subst' (h : expr) : tactic Unit := do
  let e ←
    do
      let t
        ←-- we first find the variable being substituted away
            infer_type
            h
      let (f, args) := t.get_app_fn_args
      if f = `eq ∨ f = `heq then do
          let lhs := args 1
          let rhs := args
          if rhs then return rhs
            else
              if lhs then return lhs
              else fail "subst tactic failed, hypothesis '{h.local_pp_name}' is not of the form (x = t) or (t = x)."
        else return h
  success_if_fail (is_local_def e) <|>
      fail
        f! "Cannot substitute variable {e}, it is a local definition. If you really want to do this, use `clear_value` first."
  subst h

/-- A variant of `simplify_bottom_up`. Given a tactic `post` for rewriting subexpressions,
`simp_bottom_up post e` tries to rewrite `e` starting at the leaf nodes. Returns the resulting
expression and a proof of equality. -/
unsafe def simp_bottom_up' (post : expr → tactic (expr × expr)) (e : expr) (cfg : SimpConfig := {  }) :
    tactic (expr × expr) :=
  Prod.snd <$> simplify_bottom_up () (fun _ => (· <$> ·) (Prod.mk ()) ∘ post) e cfg

/-- Caches unary type classes on a type `α : Type.{univ}`. -/
unsafe structure instance_cache where
  α : expr
  Univ : level
  inst : name_map expr

/-- Creates an `instance_cache` for the type `α`. -/
unsafe def mk_instance_cache (α : expr) : tactic instance_cache := do
  let u ← mk_meta_univ
  infer_type α >>= unify (expr.sort (level.succ u))
  let u ← get_univ_assignment u
  return ⟨α, u, mk_name_map⟩

namespace InstanceCache

/-- If `n` is the name of a type class with one parameter, `get c n` tries to find an instance of
`n c.α` by checking the cache `c`. If there is no entry in the cache, it tries to find the instance
via type class resolution, and updates the cache. -/
unsafe def get (c : instance_cache) (n : Name) : tactic (instance_cache × expr) :=
  match c.inst.find n with
  | some i => return (c, i)
  | none => do
    let e ← mk_app n [c.α] >>= mk_instance
    return (⟨c, c, c n e⟩, e)

open Expr

/-- If `e` is a `pi` expression that binds an instance-implicit variable of type `n`,
`append_typeclasses e c l` searches `c` for an instance `p` of type `n` and returns `p :: l`. -/
unsafe def append_typeclasses : expr → instance_cache → List expr → tactic (instance_cache × List expr)
  | pi _ BinderInfo.inst_implicit (app (const n _) (var _)) body, c, l => do
    let (c, p) ← c.get n
    return (c, p :: l)
  | _, c, l => return (c, l)

/-- Creates the application `n c.α p l`, where `p` is a type class instance found in the cache `c`.
-/
unsafe def mk_app (c : instance_cache) (n : Name) (l : List expr) : tactic (instance_cache × expr) := do
  let d ← get_decl n
  let (c, l) ← append_typeclasses d.type.binding_body c l
  return (c, (expr.const n [c]).mk_app (c :: l))

/-- `c.of_nat n` creates the `c.α`-valued numeral expression corresponding to `n`. -/
protected unsafe def of_nat (c : instance_cache) (n : ℕ) : tactic (instance_cache × expr) :=
  if n = 0 then c.mk_app `` Zero.zero []
  else do
    let (c, ai) ← c.get `` Add
    let (c, oi) ← c.get `` One
    let (c, one) ← c.mk_app `` One.one []
    return
        (c,
          (n one) fun b n e =>
            if n = 0 then one
            else cond b ((expr.const `` bit1 [c]).mk_app [c, oi, ai, e]) ((expr.const `` bit0 [c]).mk_app [c, ai, e]))

/-- `c.of_int n` creates the `c.α`-valued numeral expression corresponding to `n`.
The output is either a numeral or the negation of a numeral. -/
protected unsafe def of_int (c : instance_cache) : ℤ → tactic (instance_cache × expr)
  | (n : ℕ) => c.ofNat n
  | -[1+ n] => do
    let (c, e) ← c.ofNat (n + 1)
    c `` Neg.neg [e]

end InstanceCache

/-- A variation on `assert` where a (possibly incomplete)
proof of the assertion is provided as a parameter.

``(h,gs) ← local_proof `h p tac`` creates a local `h : p` and
use `tac` to (partially) construct a proof for it. `gs` is the
list of remaining goals in the proof of `h`.

The benefits over assert are:
- unlike with ``h ← assert `h p, tac`` , `h` cannot be used by `tac`;
- when `tac` does not complete the proof of `h`, returning the list
  of goals allows one to write a tactic using `h` and with the confidence
  that a proof will not boil over to goals left over from the proof of `h`,
  unlike what would be the case when using `tactic.swap`.
-/
unsafe def local_proof (h : Name) (p : expr) (tac₀ : tactic Unit) : tactic (expr × List expr) :=
  focus1 <| do
    let h' ← assert h p
    let [g₀, g₁] ← get_goals
    set_goals [g₀]
    tac₀
    let gs ← get_goals
    set_goals [g₁]
    return (h', gs)

/-- `var_names e` returns a list of the unique names of the initial pi bindings in `e`. -/
unsafe def var_names : expr → List Name
  | expr.pi n _ _ b => n :: var_names b
  | _ => []

/-- When `struct_n` is the name of a structure type,
`subobject_names struct_n` returns two lists of names `(instances, fields)`.
The names in `instances` are the projections from `struct_n` to the structures that it extends
(assuming it was defined with `old_structure_cmd false`).
The names in `fields` are the standard fields of `struct_n`. -/
unsafe def subobject_names (struct_n : Name) : tactic (List Name × List Name) := do
  let env ← get_env
  let c ←
    match env.constructors_of struct_n with
      | [c] => pure c
      | [] =>
        if env.is_inductive struct_n then fail f! "{struct_n} does not have constructors"
        else fail f! "{struct_n} is not an inductive type"
      | _ => fail "too many constructors"
  let vs ← var_names <$> (mk_const c >>= infer_type)
  let fields ← env.structure_fields struct_n
  return <| fields fun fn => ↑("_" ++ fn) ∈ vs

private unsafe def expanded_field_list' : Name → tactic (Dlist <| Name × Name)
  | struct_n => do
    let (so, fs) ← subobject_names struct_n
    let ts ←
      so.mmap fun n => do
          let (_, e) ← mk_const (n.updatePrefix struct_n) >>= infer_type >>= open_pis
          expanded_field_list' <| e
    return <| Dlist.join ts ++ Dlist.ofList (fs <| Prod.mk struct_n)

open Functor Function

/-- `expanded_field_list struct_n` produces a list of the names of the fields of the structure
named `struct_n`. These are returned as pairs of names `(prefix, name)`, where the full name
of the projection is `prefix.name`.

`struct_n` cannot be a synonym for a `structure`, it must be itself a `structure` -/
unsafe def expanded_field_list (struct_n : Name) : tactic (List <| Name × Name) :=
  Dlist.toList <$> expanded_field_list' struct_n

/-- Return a list of all type classes which can be instantiated
for the given expression.
-/
unsafe def get_classes (e : expr) : tactic (List Name) :=
  attribute.get_instances `class >>= List.mfilter fun n => succeeds <| mk_app n [e] >>= mk_instance

/-- Finds an instance of an implication `cond → tgt`.
Returns a pair of a local constant `e` of type `cond`, and an instance of `tgt` that can mention
`e`. The local constant `e` is added as an hypothesis to the tactic state, but should not be used,
since it has been "proven" by a metavariable.
-/
unsafe def mk_conditional_instance (cond tgt : expr) : tactic (expr × expr) := do
  let f ← mk_meta_var cond
  let e ← assertv `c cond f
  swap
  reset_instance_cache
  let inst ← mk_instance tgt
  return (e, inst)

open Nat

/-- Create a list of `n` fresh metavariables. -/
unsafe def mk_mvar_list : ℕ → tactic (List expr)
  | 0 => pure []
  | succ n => (· :: ·) <$> mk_mvar <*> mk_mvar_list n

/-- Returns the only goal, or fails if there isn't just one goal. -/
unsafe def get_goal : tactic expr := do
  let gs ← get_goals
  match gs with
    | [a] => return a
    | [] => fail "there are no goals"
    | _ => fail "there are too many goals"

/-- `iterate_at_most_on_all_goals n t`: repeat the given tactic at most `n` times on all goals,
or until it fails. Always succeeds. -/
unsafe def iterate_at_most_on_all_goals : Nat → tactic Unit → tactic Unit
  | 0, tac => trace "maximal iterations reached"
  | succ n, tac =>
    tactic.all_goals' <|
      (do
          tac
          iterate_at_most_on_all_goals n tac) <|>
        skip

/-- `iterate_at_most_on_subgoals n t`: repeat the tactic `t` at most `n` times on the first
goal and on all subgoals thus produced, or until it fails. Fails iff `t` fails on
current goal. -/
unsafe def iterate_at_most_on_subgoals : Nat → tactic Unit → tactic Unit
  | 0, tac => trace "maximal iterations reached"
  | succ n, tac =>
    focus1 do
      tac
      iterate_at_most_on_all_goals n tac

/-- This makes sure that the execution of the tactic does not change the tactic state.
This can be helpful while using rewrite, apply, or expr munging.
Remember to instantiate your metavariables before you're done! -/
unsafe def lock_tactic_state {α} (t : tactic α) : tactic α
  | s =>
    match t s with
    | result.success a s' => result.success a s
    | result.exception msg Pos s' => result.exception msg Pos s

/-- `apply_list l`, for `l : list (tactic expr)`,
tries to apply the lemmas generated by the tactics in `l` on the first goal, and
fail if none succeeds.
-/
unsafe def apply_list_expr (opt : ApplyCfg) : List (tactic expr) → tactic Unit
  | [] => fail "no matching rule"
  | h :: t =>
    (do
        let e ← h
        interactive.concat_tags (apply e opt)) <|>
      apply_list_expr t

/-- Given the name of a user attribute, produces a list of `tactic expr`s, each of which is the
application of `i_to_expr_for_apply` to a declaration with that attribute.
-/
unsafe def resolve_attribute_expr_list (attr_name : Name) : tactic (List (tactic expr)) := do
  let l ← attribute.get_instances attr_name
  List.map i_to_expr_for_apply <$> List.reverse <$> l resolve_name

/-- `apply_rules args attrs n`: apply the lists of rules `args` (given as pexprs) and `attrs` (given
as names of attributes) and `the tactic assumption` on the first goal and the resulting subgoals,
iteratively, at most `n` times.

Unlike `solve_by_elim`, `apply_rules` does not do any backtracking, and just greedily applies
a lemma from the list until it can't.
 -/
unsafe def apply_rules (args : List pexpr) (attrs : List Name) (n : Nat) (opt : ApplyCfg) : tactic Unit := do
  let attr_exprs ← lock_tactic_state <| attrs.mfoldl (fun l n => List.append l <$> resolve_attribute_expr_list n) []
  let args_exprs := args.map i_to_expr_for_apply ++ attr_exprs
  -- `args_exprs` is a list of `tactic expr`, rather than just `expr`, because these expressions will
      -- be repeatedly applied against goals, and we need to ensure that metavariables don't get stuck.
      iterate_at_most_on_subgoals
      n (assumption <|> apply_list_expr opt args_exprs)

/-- `replace h p` elaborates the pexpr `p`, clears the existing hypothesis named `h` from the local
context, and adds a new hypothesis named `h`. The type of this hypothesis is the type of `p`.
Fails if there is nothing named `h` in the local context. -/
unsafe def replace (h : Name) (p : pexpr) : tactic Unit := do
  let h' ← get_local h
  let p ← to_expr p
  note h none p
  clear h'

/-- Auxiliary function for `iff_mp` and `iff_mpr`. Takes a name, which should be either `` `iff.mp``
or `` `iff.mpr``. If the passed expression is an iterated function type eventually producing an
`iff`, returns an expression with the `iff` converted to either the forwards or backwards
implication, as requested. -/
unsafe def mk_iff_mp_app (iffmp : Name) : expr → (Nat → expr) → Option expr
  | expr.pi n bi e t, f => expr.lam n bi e <$> mk_iff_mp_app t fun n => f (n + 1) (expr.var n)
  | quote.1 ((%%ₓa) ↔ %%ₓb), f => some <| @expr.const true iffmp [] a b (f 0)
  | _, f => none

/-- `iff_mp_core e ty` assumes that `ty` is the type of `e`.
If `ty` has the shape `Π ..., A ↔ B`, returns an expression whose type is `Π ..., A → B`. -/
unsafe def iff_mp_core (e ty : expr) : Option expr :=
  mk_iff_mp_app `iff.mp ty fun _ => e

/-- `iff_mpr_core e ty` assumes that `ty` is the type of `e`.
If `ty` has the shape `Π ..., A ↔ B`, returns an expression whose type is `Π ..., B → A`. -/
unsafe def iff_mpr_core (e ty : expr) : Option expr :=
  mk_iff_mp_app `iff.mpr ty fun _ => e

/-- Given an expression whose type is (a possibly iterated function producing) an `iff`,
create the expression which is the forward implication. -/
unsafe def iff_mp (e : expr) : tactic expr := do
  let t ← infer_type e
  iff_mp_core e t <|> fail "Target theorem must have the form `Π x y z, a ↔ b`"

/-- Given an expression whose type is (a possibly iterated function producing) an `iff`,
create the expression which is the reverse implication. -/
unsafe def iff_mpr (e : expr) : tactic expr := do
  let t ← infer_type e
  iff_mpr_core e t <|> fail "Target theorem must have the form `Π x y z, a ↔ b`"

/-- Attempts to apply `e`, and if that fails, if `e` is an `iff`,
try applying both directions separately.
-/
unsafe def apply_iff (e : expr) : tactic (List (Name × expr)) :=
  let ap (e) := tactic.apply e { NewGoals := NewGoals.non_dep_only }
  ap e <|> iff_mp e >>= ap <|> iff_mpr e >>= ap

/-- Configuration options for `apply_any`:
* `use_symmetry`: if `apply_any` fails to apply any lemma, call `symmetry` and try again.
* `use_exfalso`: if `apply_any` fails to apply any lemma, call `exfalso` and try again.
* `apply`: specify an alternative to `tactic.apply`; usually `apply := tactic.eapply`.
-/
unsafe structure apply_any_opt extends ApplyCfg where
  use_symmetry : Bool := true
  use_exfalso : Bool := true

/-- This is a version of `apply_any` that takes a list of `tactic expr`s instead of `expr`s,
and evaluates these as thunks before trying to apply them.

We need to do this to avoid metavariables getting stuck during subsequent rounds of `apply`.
-/
unsafe def apply_any_thunk (lemmas : List (tactic expr)) (opt : apply_any_opt := {  }) (tac : tactic Unit := skip)
    (on_success : expr → tactic Unit := fun _ => skip) (on_failure : tactic Unit := skip) : tactic Unit := do
  let modes := ([skip] ++ if opt.use_symmetry then [symmetry] else []) ++ if opt.use_exfalso then [exfalso] else []
  (modes fun m => do
        m
        lemmas fun H =>
            H >>= fun e => do
              apply e opt
              on_success e
              tac) <|>
      on_failure >> fail "apply_any tactic failed; no lemma could be applied"

/-- `apply_any lemmas` tries to apply one of the list `lemmas` to the current goal.

`apply_any lemmas opt` allows control over how lemmas are applied.
`opt` has fields:
* `use_symmetry`: if no lemma applies, call `symmetry` and try again. (Defaults to `tt`.)
* `use_exfalso`: if no lemma applies, call `exfalso` and try again. (Defaults to `tt`.)
* `apply`: use a tactic other than `tactic.apply` (e.g. `tactic.fapply` or `tactic.eapply`).

`apply_any lemmas tac` calls the tactic `tac` after a successful application.
Defaults to `skip`. This is used, for example, by `solve_by_elim` to arrange
recursive invocations of `apply_any`.
-/
unsafe def apply_any (lemmas : List expr) (opt : apply_any_opt := {  }) (tac : tactic Unit := skip) : tactic Unit :=
  apply_any_thunk (lemmas.map pure) opt tac

/-- Try to apply a hypothesis from the local context to the goal. -/
unsafe def apply_assumption : tactic Unit :=
  local_context >>= apply_any

/-- `change_core e none` is equivalent to `change e`. It tries to change the goal to `e` and fails
if this is not a definitional equality.

`change_core e (some h)` assumes `h` is a local constant, and tries to change the type of `h` to `e`
by reverting `h`, changing the goal, and reintroducing hypotheses. -/
unsafe def change_core (e : expr) : Option expr → tactic Unit
  | none => tactic.change e
  | some h => do
    let num_reverted : ℕ ← revert h
    let expr.pi n bi d b ← target
    tactic.change <| expr.pi n bi e b
    intron num_reverted

/-- `change_with_at olde newe hyp` replaces occurences of `olde` with `newe` at hypothesis `hyp`,
assuming `olde` and `newe` are defeq when elaborated.
-/
unsafe def change_with_at (olde newe : pexpr) (hyp : Name) : tactic Unit := do
  let h ← get_local hyp
  let tp ← infer_type h
  let olde ← to_expr olde
  let newe ← to_expr newe
  let repl_tp := tp.replace fun a n => if a = olde then some newe else none
  when (repl_tp ≠ tp) <| change_core repl_tp (some h)

/-- Returns a list of all metavariables in the current partial proof. This can differ from
the list of goals, since the goals can be manually edited. -/
unsafe def metavariables : tactic (List expr) :=
  expr.list_meta_vars <$> result

/-- `sorry_if_contains_sorry` will solve any goal already containing `sorry` in its type with `sorry`,
and fail otherwise.
-/
unsafe def sorry_if_contains_sorry : tactic Unit := do
  let g ← target
  guardₓ g <|> fail "goal does not contain `sorry`"
  tactic.admit

/-- Fail if the target contains a metavariable. -/
unsafe def no_mvars_in_target : tactic Unit :=
  expr.has_meta_var <$> target >>= guardb ∘ bnot

/-- Succeeds only if the current goal is a proposition. -/
unsafe def propositional_goal : tactic Unit := do
  let g :: _ ← get_goals
  is_proof g >>= guardb

/-- Succeeds only if we can construct an instance showing the
  current goal is a subsingleton type. -/
unsafe def subsingleton_goal : tactic Unit := do
  let g :: _ ← get_goals
  let ty ← infer_type g >>= instantiate_mvars
  (to_expr (pquote.1 (Subsingleton (%%ₓty))) >>= mk_instance) >> skip

/-- Succeeds only if the current goal is "terminal",
in the sense that no other goals depend on it
(except possibly through shared metavariables; see `independent_goal`).
-/
unsafe def terminal_goal : tactic Unit :=
  propositional_goal <|>
    subsingleton_goal <|> do
      let g₀ :: _ ← get_goals
      let mvars ← (fun L => List.eraseₓ L g₀) <$> metavariables
      mvars fun g => do
          let t ← infer_type g >>= instantiate_mvars
          let d ← kdepends_on t g₀
          Monadₓ.whenb d <| pp t >>= fun s => fail ("The current goal is not terminal: " ++ s ++ " depends on it.")

/-- Succeeds only if the current goal is "independent", in the sense
that no other goals depend on it, even through shared meta-variables.
-/
unsafe def independent_goal : tactic Unit :=
  no_mvars_in_target >> terminal_goal

/-- `triv'` tries to close the first goal with the proof `trivial : true`. Unlike `triv`,
it only unfolds reducible definitions, so it sometimes fails faster. -/
unsafe def triv' : tactic Unit := do
  let c ← mk_const `trivial
  exact c reducible

variable {α : Type}

/-- Apply a tactic as many times as possible, collecting the results in a list.
Fail if the tactic does not succeed at least once. -/
unsafe def iterate1 (t : tactic α) : tactic (List α) := do
  let r ← decorate_ex "iterate1 failed: tactic did not succeed" t
  let L ← iterate t
  return (r :: L)

/-- Introduces one or more variables and returns the new local constants.
Fails if `intro` cannot be applied. -/
unsafe def intros1 : tactic (List expr) :=
  iterate1 intro1

/-- Run a tactic "under binders", by running `intros` before, and `revert` afterwards. -/
unsafe def under_binders {α : Type} (t : tactic α) : tactic α := do
  let v ← intros
  let r ← t
  revert_lst v
  return r

namespace Interactive

/-- Run a tactic "under binders", by running `intros` before, and `revert` afterwards. -/
unsafe def under_binders (i : itactic) : itactic :=
  tactic.under_binders i

end Interactive

/-- `successes` invokes each tactic in turn, returning the list of successful results. -/
unsafe def successes (tactics : List (tactic α)) : tactic (List α) :=
  List.filterMap id <$> Monadₓ.sequence (tactics.map fun t => try_core t)

/-- Try all the tactics in a list, each time starting at the original `tactic_state`,
returning the list of successful results,
and reverting to the original `tactic_state`.
-/
-- Note this is not the same as `successes`, which keeps track of the evolving `tactic_state`.
unsafe def try_all {α : Type} (tactics : List (tactic α)) : tactic (List α) := fun s =>
  result.success
    (tactics.map fun t : tactic α =>
        match t s with
        | result.success a s' => [a]
        | _ => []).join
    s

/-- Try all the tactics in a list, each time starting at the original `tactic_state`,
returning the list of successful results sorted by
the value produced by a subsequent execution of the `sort_by` tactic,
and reverting to the original `tactic_state`.
-/
unsafe def try_all_sorted {α : Type} (tactics : List (tactic α)) (sort_by : tactic ℕ := num_goals) :
    tactic (List (α × ℕ)) := fun s =>
  result.success
    ((tactics.map fun t : tactic α =>
            match
              (do
                  let a ← t
                  let n ← sort_by
                  return (a, n))
                s with
            | result.success a s' => [a]
            | _ => []).join.qsort
      fun p q : α × ℕ => p.2 < q.2)
    s

/-- Return target after instantiating metavars and whnf. -/
private unsafe def target' : tactic expr :=
  target >>= instantiate_mvars >>= whnf

/-- Just like `split`, `fsplit` applies the constructor when the type of the target is
an inductive data type with one constructor.
However it does not reorder goals or invoke `auto_param` tactics.
-/
-- FIXME check if we can remove `auto_param := ff`
unsafe def fsplit : tactic Unit := do
  let [c] ← target' >>= get_constructors_for |
    fail "fsplit tactic failed, target is not an inductive datatype with only one constructor"
  mk_const c >>= fun e => apply e { NewGoals := new_goals.all, AutoParam := ff } >> skip

run_cmd
  add_interactive [`fsplit]

add_tactic_doc
  { Name := "fsplit", category := DocCategory.tactic, declNames := [`tactic.interactive.fsplit],
    tags := ["logic", "goal management"] }

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `results
/-- Calls `injection` on each hypothesis, and then, for each hypothesis on which `injection`
succeeds, clears the old hypothesis. -/
unsafe def injections_and_clear : tactic Unit := do
  let l ← local_context
  let results ← successes <| l.map fun e => injection e >> clear e
  when (results results.empty) (fail "could not use `injection` then `clear` on any hypothesis")

run_cmd
  add_interactive [`injections_and_clear]

add_tactic_doc
  { Name := "injections_and_clear", category := DocCategory.tactic,
    declNames := [`tactic.interactive.injections_and_clear], tags := ["context management"] }

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `r
/-- Calls `cases` on every local hypothesis, succeeding if
it succeeds on at least one hypothesis. -/
unsafe def case_bash : tactic Unit := do
  let l ← local_context
  let r ← successes (l.reverse.map fun h => cases h >> skip)
  when (r r.empty) failed

/-- `note_anon t v`, given a proof `v : t`,
adds `h : t` to the current context, where the name `h` is fresh.

`note_anon none v` will infer the type `t` from `v`.
-/
-- While `note` provides a default value for `t`, it doesn't seem this could ever be used.
unsafe def note_anon (t : Option expr) (v : expr) : tactic expr := do
  let h ← get_unused_name `h none
  note h t v

/-- `find_local t` returns a local constant with type t, or fails if none exists. -/
unsafe def find_local (t : pexpr) : tactic expr := do
  let t' ← to_expr t
  Prod.snd <$> solve_aux t' assumption >>= instantiate_mvars <|> fail f! "No hypothesis found of the form: {t'}"

/-- `dependent_pose_core l`: introduce dependent hypotheses, where the proofs depend on the values
of the previous local constants. `l` is a list of local constants and their values. -/
unsafe def dependent_pose_core (l : List (expr × expr)) : tactic Unit := do
  let lc := l.map Prod.fst
  let lm := l.map fun ⟨l, v⟩ => (l.local_uniq_name, v)
  let old :: other_goals ← get_goals
  let t ← infer_type old
  let new_goal ← mk_meta_var (t.pis lc)
  set_goals (old :: new_goal :: other_goals)
  exact ((new_goal lc).instantiate_locals lm)
  return ()

/-- Instantiates metavariables that appear in the current goal.
-/
unsafe def instantiate_mvars_in_target : tactic Unit :=
  target >>= instantiate_mvars >>= change

/-- Instantiates metavariables in all goals.
-/
unsafe def instantiate_mvars_in_goals : tactic Unit :=
  all_goals' <| instantiate_mvars_in_target

/-- Protect the declaration `n` -/
unsafe def mk_protected (n : Name) : tactic Unit := do
  let env ← get_env
  set_env (env n)

end Tactic

namespace Lean.Parser

open Tactic InteractionMonad

/-- A version of `lean.parser.many` that requires at least `n` items -/
unsafe def repeat_at_least {α : Type} (p : lean.parser α) : ℕ → lean.parser (List α)
  | 0 => many p
  | n + 1 => List.cons <$> p <*> repeat_at_least n

/-- A version of `lean.parser.sep_by` that allows trailing delimiters, but requires at least one
item. Like `lean.parser.sep_by`, as a result of the `lean.parser` monad not being pure, this is only
well-behaved if `p` and `s` are backtrackable; which in practice means they must not consume the
input when they do not have a match. -/
unsafe def sep_by_trailing {α : Type} (s : lean.parser Unit) (p : lean.parser α) : lean.parser (List α) := do
  let fst ← p
  let some () ← optionalₓ s | pure [fst]
  let some rest ← optionalₓ sep_by_trailing | pure [fst]
  pure (fst :: rest)

/-- `emit_command_here str` behaves as if the string `str` were placed as a user command at the
current line. -/
unsafe def emit_command_here (str : Stringₓ) : lean.parser Stringₓ := do
  let (_, left) ← with_input command_like str
  return left

/-- Inner recursion for `emit_code_here`. -/
unsafe def emit_code_here_aux : Stringₓ → ℕ → lean.parser Unit
  | str, slen => do
    let left ← emit_command_here str
    let llen := left.length
    when (llen < slen ∧ llen ≠ 0) (emit_code_here_aux left llen)

/-- `emit_code_here str` behaves as if the string `str` were placed at the current location in
source code. -/
unsafe def emit_code_here (s : Stringₓ) : lean.parser Unit :=
  emit_code_here_aux s s.length

/-- `run_parser p` is like `run_cmd` but for the parser monad. It executes parser `p` at the
top level, giving access to operations like `emit_code_here`. -/
@[user_command]
unsafe def run_parser_cmd (_ : interactive.parse <| tk "run_parser") : lean.parser Unit := do
  let e ← lean.parser.pexpr 0
  let p ← eval_pexpr (lean.parser Unit) e
  p

add_tactic_doc
  { Name := "run_parser", category := DocCategory.cmd, declNames := [`` run_parser_cmd], tags := ["parsing"] }

/-- `get_current_namespace` returns the current namespace (it could be `name.anonymous`).

This function deserves a C++ implementation in core lean, and will fail if it is not called from
the body of a command (i.e. anywhere else that the `lean.parser` monad can be invoked). -/
unsafe def get_current_namespace : lean.parser Name := do
  let env ← get_env
  let n ← tactic.mk_user_fresh_name
  emit_code_here <| s! "def {n} := ()"
  let nfull ← tactic.resolve_constant n
  set_env env
  return <| nfull n

/-- `get_variables` returns a list of existing variable names, along with their types and binder
info. -/
unsafe def get_variables : lean.parser (List (Name × BinderInfo × expr)) :=
  List.map expr.get_local_const_kind <$> list_available_include_vars

/-- `get_included_variables` returns those variables `v` returned by `get_variables` which have been
"included" by an `include v` statement and are not (yet) `omit`ed. -/
unsafe def get_included_variables : lean.parser (List (Name × BinderInfo × expr)) := do
  let ns ← list_include_var_names
  (List.filterₓ fun v => v.1 ∈ ns) <$> get_variables

/-- From the `lean.parser` monad, synthesize a `tactic_state` which includes all of the local
variables referenced in `es : list pexpr`, and those variables which have been `include`ed in the
local context---precisely those variables which would be ambiently accessible if we were in a
tactic-mode block where the goals had types `es.mmap to_expr`, for example.

Returns a new `ts : tactic_state` with these local variables added, and
`mappings : list (expr × expr)`, for which pairs `(var, hyp)` correspond to an existing variable
`var` and the local hypothesis `hyp` which was added to the tactic state `ts` as a result. -/
unsafe def synthesize_tactic_state_with_variables_as_hyps (es : List pexpr) :
    lean.parser (tactic_state × List (expr × expr)) := do
  let vars
    ←/- First, in order to get `to_expr e` to resolve declared `variables`, we add all of the
            declared variables to a fake `tactic_state`, and perform the resolution. At the end,
            `to_expr e` has done the work of determining which variables were actually referenced, which
            we then obtain from `fe` via `expr.list_local_consts` (which, importantly, is not defined for
            `pexpr`s). -/
      list_available_include_vars
  let fake_es ←
    lean.parser.of_tactic <|
        lock_tactic_state <| do
          /- Note that `add_local_consts_as_local_hyps` returns the mappings it generated, but we discard
                      them on this first pass. (We return the mappings generated by our second invocation of this
                      function below.) -/
              add_local_consts_as_local_hyps
              vars
          es to_expr
  let included_vars
    ←/- Now calculate lists of a) the explicitly `include`ed variables and b) the variables which were
            referenced in `e` when it was resolved to `fake_e`.
      
            It is important that we include variables of the kind a) because we want `simp` to have access
            to declared local instances, and it is important that we only restrict to variables of kind a)
            and b) together since we do not to recognise a hypothesis which is posited as a `variable`
            in the environment but not referenced in the `pexpr` we were passed.
      
            One use case for this behaviour is running `simp` on the passed `pexpr`, since we do not want
            simp to use arbitrary hypotheses which were declared as `variables` in the local environment
            but not referenced in the expression to simplify (as one would be expect generally in tactic
            mode). -/
      list_include_var_names
  let referenced_vars := List.join <| fake_es.map fun e => e.list_local_consts.map expr.local_pp_name
  let/- Look up the explicit `included_vars` and the `referenced_vars` (which have appeared in the
        `pexpr` list which we were passed.)  -/
  directly_included_vars :=
    vars.filter fun var => var.local_pp_name ∈ included_vars ∨ var.local_pp_name ∈ referenced_vars
  let/- Inflate the list `directly_included_vars` to include those variables which are "implicitly
        included" by virtue of reference to one or multiple others. For example, given
        `variables (n : ℕ) [prime n] [ih : even n]`, a reference to `n` implies that the typeclass
        instance `prime n` should be included, but `ih : even n` should not. -/
  all_implicitly_included_vars := expr.all_implicitly_included_variables vars directly_included_vars
  /- Capture a tactic state where both of these kinds of variables have been added as local
            hypotheses, and resolve `e` against this state with `to_expr`, this time for real. -/
      lean.parser.of_tactic <|
      do
      let mappings ← add_local_consts_as_local_hyps all_implicitly_included_vars
      let ts ← get_state
      return (ts, mappings)

end Lean.Parser

namespace Tactic

variable {α : Type}

/-- Hole command used to fill in a structure's field when specifying an instance.

In the following:

```lean
instance : monad id :=
{! !}
```

invoking the hole command "Instance Stub" ("Generate a skeleton for the structure under
construction.") produces:

```lean
instance : monad id :=
{ map := _,
  map_const := _,
  pure := _,
  seq := _,
  seq_left := _,
  seq_right := _,
  bind := _ }
```
-/
@[hole_command]
unsafe def instance_stub : hole_command where
  Name := "Instance Stub"
  descr := "Generate a skeleton for the structure under construction."
  action := fun _ => do
    let tgt ← target >>= whnf
    let cl := tgt.get_app_fn.const_name
    let env ← get_env
    let fs ← expanded_field_list cl
    let fs := fs.map Prod.snd
    let fs := format.intercalate (",\n  " : format) <| fs.map fun fn => f! "{fn} := _"
    let out := format.to_string f! "\{ {fs} }}"
    return [(out, "")]

add_tactic_doc
  { Name := "instance_stub", category := DocCategory.hole_cmd, declNames := [`tactic.instance_stub],
    tags := ["instances"] }

/-- Like `resolve_name` except when the list of goals is
empty. In that situation `resolve_name` fails whereas
`resolve_name'` simply proceeds on a dummy goal -/
unsafe def resolve_name' (n : Name) : tactic pexpr := do
  let [] ← get_goals | resolve_name n
  let g ← mk_mvar
  set_goals [g]
  resolve_name n <* set_goals []

private unsafe def strip_prefix' (n : Name) : List Stringₓ → Name → tactic Name
  | s, Name.anonymous => pure <| s.foldl (flip Name.mk_string) Name.anonymous
  | s, Name.mk_string a p => do
    let n' := s.foldl (flip Name.mk_string) Name.anonymous
    (do
          let n'' ← tactic.resolve_constant n'
          if n'' = n then pure n' else strip_prefix' (a :: s) p) <|>
        strip_prefix' (a :: s) p
  | s, n@(Name.mk_numeral a p) => pure <| s.foldl (flip Name.mk_string) n

/-- Strips unnecessary prefixes from a name, e.g. if a namespace is open. -/
unsafe def strip_prefix : Name → tactic Name
  | n@(Name.mk_string a a_1) =>
    if `_private.isPrefixOf n then
      let n' := n.updatePrefix Name.anonymous
      n' <$ resolve_name' n' <|> pure n
    else strip_prefix' n [a] a_1
  | n => pure n

/-- Used to format return strings for the hole commands `match_stub` and `eqn_stub`. -/
unsafe def mk_patterns (t : expr) : tactic (List format) := do
  let cl := t.get_app_fn.const_name
  let env ← get_env
  let fs := env.constructors_of cl
  fs fun f => do
      let (vs, _) ← mk_const f >>= infer_type >>= open_pis
      let vs := vs fun v => v
      let vs ←
        vs fun v => do
            let v' ← get_unused_name v
            pose v' none (quote.1 ())
            pure v'
      vs fun v => get_local v >>= clear
      let args := List.intersperse (" " : format) <| vs to_fmt
      let f ← strip_prefix f
      if args then
          pure <|
            f! "| {f} := _
              "
        else
          pure
            f! "| ({f } {format.join args}) := _
              "

/-- Hole command used to generate a `match` expression.

In the following:

```lean
meta def foo (e : expr) : tactic unit :=
{! e !}
```

invoking hole command "Match Stub" ("Generate a list of equations for a `match` expression")
produces:

```lean
meta def foo (e : expr) : tactic unit :=
match e with
| (expr.var a) := _
| (expr.sort a) := _
| (expr.const a a_1) := _
| (expr.mvar a a_1 a_2) := _
| (expr.local_const a a_1 a_2 a_3) := _
| (expr.app a a_1) := _
| (expr.lam a a_1 a_2 a_3) := _
| (expr.pi a a_1 a_2 a_3) := _
| (expr.elet a a_1 a_2 a_3) := _
| (expr.macro a a_1) := _
end
```
-/
@[hole_command]
unsafe def match_stub : hole_command where
  Name := "Match Stub"
  descr := "Generate a list of equations for a `match` expression."
  action := fun es => do
    let [e] ← pure es | fail "expecting one expression"
    let e ← to_expr e
    let t ← infer_type e >>= whnf
    let fs ← mk_patterns t
    let e ← pp e
    let out :=
      format.to_string
        f! "match {e } with
          {format.join fs}end
          "
    return [(out, "")]

add_tactic_doc
  { Name := "Match Stub", category := DocCategory.hole_cmd, declNames := [`tactic.match_stub],
    tags := ["pattern matching"] }

/-- Invoking hole command "Equations Stub" ("Generate a list of equations for a recursive definition")
in the following:

```lean
meta def foo : {! expr → tactic unit !} -- `:=` is omitted
```

produces:

```lean
meta def foo : expr → tactic unit
| (expr.var a) := _
| (expr.sort a) := _
| (expr.const a a_1) := _
| (expr.mvar a a_1 a_2) := _
| (expr.local_const a a_1 a_2 a_3) := _
| (expr.app a a_1) := _
| (expr.lam a a_1 a_2 a_3) := _
| (expr.pi a a_1 a_2 a_3) := _
| (expr.elet a a_1 a_2 a_3) := _
| (expr.macro a a_1) := _
```

A similar result can be obtained by invoking "Equations Stub" on the following:

```lean
meta def foo : expr → tactic unit := -- do not forget to write `:=`!!
{! !}
```

```lean
meta def foo : expr → tactic unit := -- don't forget to erase `:=`!!
| (expr.var a) := _
| (expr.sort a) := _
| (expr.const a a_1) := _
| (expr.mvar a a_1 a_2) := _
| (expr.local_const a a_1 a_2 a_3) := _
| (expr.app a a_1) := _
| (expr.lam a a_1 a_2 a_3) := _
| (expr.pi a a_1 a_2 a_3) := _
| (expr.elet a a_1 a_2 a_3) := _
| (expr.macro a a_1) := _
```

-/
@[hole_command]
unsafe def eqn_stub : hole_command where
  Name := "Equations Stub"
  descr := "Generate a list of equations for a recursive definition."
  action := fun es => do
    let t ←
      match es with
        | [t] => to_expr t
        | [] => target
        | _ => fail "expecting one type"
    let e ← whnf t
    let (v :: _, _) ← open_pis e | fail "expecting a Pi-type"
    let t' ← infer_type v
    let fs ← mk_patterns t'
    let t ← pp t
    let out :=
      if es.Empty then
        format.to_string
          f! "-- do not forget to erase `:=`!!
            {format.join fs}"
      else
        format.to_string
          f! "{t }
            {format.join fs}"
    return [(out, "")]

add_tactic_doc
  { Name := "Equations Stub", category := DocCategory.hole_cmd, declNames := [`tactic.eqn_stub],
    tags := ["pattern matching"] }

/-- This command lists the constructors that can be used to satisfy the expected type.

Invoking "List Constructors" ("Show the list of constructors of the expected type")
in the following hole:

```lean
def foo : ℤ ⊕ ℕ :=
{! !}
```

produces:

```lean
def foo : ℤ ⊕ ℕ :=
{! sum.inl, sum.inr !}
```

and will display:

```lean
sum.inl : ℤ → ℤ ⊕ ℕ

sum.inr : ℕ → ℤ ⊕ ℕ
```

-/
@[hole_command]
unsafe def list_constructors_hole : hole_command where
  Name := "List Constructors"
  descr := "Show the list of constructors of the expected type."
  action := fun es => do
    let t ← target >>= whnf
    let (_, t) ← open_pis t
    let cl := t.get_app_fn.const_name
    let args := t.get_app_args
    let env ← get_env
    let cs := env.constructors_of cl
    let ts ←
      cs.mmap fun c => do
          let e ← mk_const c
          let t ← infer_type (e.mk_app args) >>= pp
          let c ← strip_prefix c
          pure
              f! "
                {c } : {t}
                "
    let fs ← format.intercalate ", " <$> cs.mmap (strip_prefix >=> pure ∘ to_fmt)
    let out := format.to_string f! "\{! {fs} !}}"
    trace (format.join ts).toString
    return [(out, "")]

add_tactic_doc
  { Name := "List Constructors", category := DocCategory.hole_cmd, declNames := [`tactic.list_constructors_hole],
    tags := ["goal information"] }

/-- Makes the declaration `classical.prop_decidable` available to type class inference.
This asserts that all propositions are decidable, but does not have computational content.

The `aggressive` argument controls whether the instance is added globally, where it has low
priority, or in the local context, where it has very high priority. -/
unsafe def classical (aggressive : Bool := false) : tactic Unit :=
  if aggressive then do
    let h ← get_unused_name `_inst
    mk_const `classical.prop_decidable >>= note h none
    reset_instance_cache
  else do
    -- Turn on the `prop_decidable` instance. `9` is what we use in the `classical` locale
        tactic.set_basic_attribute
        `instance `classical.prop_decidable ff (some 9)

open Expr

/-- `mk_comp v e` checks whether `e` is a sequence of nested applications `f (g (h v))`, and if so,
returns the expression `f ∘ g ∘ h`. -/
unsafe def mk_comp (v : expr) : expr → tactic expr
  | app f e =>
    if e = v then pure f
    else do
      guardₓ ¬v f <|> fail "bad guard"
      let e' ← mk_comp e >>= instantiate_mvars
      let f ← instantiate_mvars f
      mk_mapp `` Function.comp [none, none, none, f, e']
  | e => do
    guardₓ (e = v)
    let t ← infer_type e
    mk_mapp `` id [t]

/-- Given two expressions `e₀` and `e₁`, return the expression `` `(%%e₀ ↔ %%e₁)``. -/
unsafe def mk_iff (e₀ : expr) (e₁ : expr) : expr :=
  quote.1 ((%%ₓe₀) ↔ %%ₓe₁)

/-- From a lemma of the shape `∀ x, f (g x) = h x`
derive an auxiliary lemma of the form `f ∘ g = h`
for reasoning about higher-order functions.
-/
unsafe def mk_higher_order_type : expr → tactic expr
  | pi n bi d b@(pi _ _ _ _) => do
    let v ← mk_local_def n d
    let b' := b.instantiate_var v
    (pi n bi d ∘ flip abstract_local v) <$> mk_higher_order_type b'
  | pi n bi d b => do
    let v ← mk_local_def n d
    let b' := b.instantiate_var v
    let (l, r) ← match_eq b' <|> fail f! "not an equality {b'}"
    let l' ← mk_comp v l
    let r' ← mk_comp v r
    mk_app `` Eq [l', r']
  | e => failed

open Lean.Parser Interactive.Types

/-- A user attribute that applies to lemmas of the shape `∀ x, f (g x) = h x`.
It derives an auxiliary lemma of the form `f ∘ g = h` for reasoning about higher-order functions.
-/
@[user_attribute]
unsafe def higher_order_attr : user_attribute Unit (Option Name) where
  Name := `higher_order
  parser := optionalₓ ident
  descr :=
    "From a lemma of the shape `∀ x, f (g x) = h x` derive an auxiliary lemma of the\nform `f ∘ g = h` for reasoning about higher-order functions."
  after_set :=
    some fun lmm _ _ => do
      let env ← get_env
      let decl ← env.get lmm
      let num := decl.univ_params.length
      let lvls := (List.iota num).map `l.append_after
      let l : expr := expr.const lmm <| lvls.map level.param
      let t ← infer_type l >>= instantiate_mvars
      let t' ← mk_higher_order_type t
      let (_, pr) ←
        solve_aux t' <| do
            intros
            applyc `` _root_.funext
            intro1
            andthen (applyc lmm) assumption
      let pr ← instantiate_mvars pr
      let lmm' ← higher_order_attr.get_param lmm
      let lmm' ← flip Name.updatePrefix lmm.getPrefix <$> lmm' <|> pure lmm.add_prime
      add_decl <| declaration.thm lmm' lvls t' (pure pr)
      copy_attribute `simp lmm lmm'
      copy_attribute `functor_norm lmm lmm'

add_tactic_doc
  { Name := "higher_order", category := DocCategory.attr, declNames := [`tactic.higher_order_attr],
    tags := ["lemma derivation"] }

attribute [higher_order map_comp_pure] map_pure

/-- Copies a definition into the `tactic.interactive` namespace to make it usable
in proof scripts. It allows one to write

```lean
@[interactive]
meta def my_tactic := ...
```

instead of

```lean
meta def my_tactic := ...

run_cmd add_interactive [``my_tactic]
```
-/
@[user_attribute]
unsafe def interactive_attr : user_attribute where
  Name := `interactive
  descr := "Put a definition in the `tactic.interactive` namespace to make it usable\nin proof scripts."
  after_set := some fun tac _ _ => add_interactive [tac]

add_tactic_doc
  { Name := "interactive", category := DocCategory.attr, declNames := [`` tactic.interactive_attr],
    tags := ["environment"] }

/-- Use `refine` to partially discharge the goal,
or call `fconstructor` and try again.
-/
private unsafe def use_aux (h : pexpr) : tactic Unit :=
  focus1 (refine h >> done) <|> fconstructor >> use_aux

/-- Similar to `existsi`, `use l` will use entries in `l` to instantiate existential obligations
at the beginning of a target. Unlike `existsi`, the pexprs in `l` are elaborated with respect to
the expected type.

```lean
example : ∃ x : ℤ, x = x :=
by tactic.use ``(42)
```

See the doc string for `tactic.interactive.use` for more information.
 -/
protected unsafe def use (l : List pexpr) : tactic Unit :=
  focus1 <|
    seq' (l.mmap' fun h => use_aux h <|> fail f! "failed to instantiate goal with {h}") instantiate_mvars_in_target

/-- `clear_aux_decl_aux l` clears all expressions in `l` that represent aux decls from the
local context. -/
unsafe def clear_aux_decl_aux : List expr → tactic Unit
  | [] => skip
  | e :: l => do
    cond e (tactic.clear e) skip
    clear_aux_decl_aux l

/-- `clear_aux_decl` clears all expressions from the local context that represent aux decls. -/
unsafe def clear_aux_decl : tactic Unit :=
  local_context >>= clear_aux_decl_aux

/-- `apply_at_aux e et [] h ht` (with `et` the type of `e` and `ht` the type of `h`)
finds a list of expressions `vs` and returns `(e.mk_args (vs ++ [h]), vs)`. -/
unsafe def apply_at_aux (arg t : expr) : List expr → expr → expr → tactic (expr × List expr)
  | vs, e, pi n bi d b =>
    (do
        let v ← mk_meta_var d
        apply_at_aux (v :: vs) (e v) (b v)) <|>
      (e arg, vs) <$ unify d t
  | vs, e, _ => failed

/-- `apply_at e h` applies implication `e` on hypothesis `h` and replaces `h` with the result. -/
unsafe def apply_at (e h : expr) : tactic Unit := do
  let ht ← infer_type h
  let et ← infer_type e
  let (h', gs') ← apply_at_aux h ht [] e et
  note h none h'
  clear h
  let gs' ← gs'.mfilter is_assigned
  let g :: gs ← get_goals
  set_goals (g :: gs' ++ gs)

/-- `symmetry_hyp h` applies `symmetry` on hypothesis `h`. -/
unsafe def symmetry_hyp (h : expr) (md := semireducible) : tactic Unit := do
  let tgt ← infer_type h
  let env ← get_env
  let r := get_app_fn tgt
  match env (const_name r) with
    | some symm => do
      let s ← mk_const symm
      apply_at s h
    | none => fail "symmetry tactic failed, target is not a relation application with the expected property."

/-- `setup_tactic_parser` is a user command that opens the namespaces used in writing
interactive tactics, and declares the local postfix notation `?` for `optional` and `*` for `many`.
It does *not* use the `namespace` command, so it will typically be used after
`namespace tactic.interactive`.
-/
@[user_command]
unsafe def setup_tactic_parser_cmd (_ : interactive.parse <| tk "setup_tactic_parser") : lean.parser Unit :=
  emit_code_here
    "\nopen _root_.lean\nopen _root_.lean.parser\nopen _root_.interactive _root_.interactive.types\n\nlocal postfix `?`:9001 := optional\nlocal postfix *:9001 := many .\n"

/-- `finally tac finalizer` runs `tac` first, then runs `finalizer` even if
`tac` fails. `finally tac finalizer` fails if either `tac` or `finalizer` fails. -/
unsafe def finally {β} (tac : tactic α) (finalizer : tactic β) : tactic α := fun s =>
  match tac s with
  | result.success r s' => (finalizer >> pure r) s'
  | result.exception msg p s' => (finalizer >> result.exception msg p) s'

/-- `on_exception handler tac` runs `tac` first, and then runs `handler` only if `tac` failed.
-/
unsafe def on_exception {β} (handler : tactic β) (tac : tactic α) : tactic α
  | s =>
    match tac s with
    | result.exception msg p s' => (handler *> result.exception msg p) s'
    | ok => ok

/-- `decorate_error add_msg tac` prepends `add_msg` to an exception produced by `tac` -/
unsafe def decorate_error (add_msg : Stringₓ) (tac : tactic α) : tactic α
  | s =>
    match tac s with
    | result.exception msg p s =>
      let msg (_ : Unit) : format :=
        match msg with
        | some msg => add_msg ++ format.line ++ msg ()
        | none => add_msg
      result.exception msg p s
    | ok => ok

/-- Applies tactic `t`. If it succeeds, revert the state, and return the value. If it fails,
  returns the error message. -/
unsafe def retrieve_or_report_error {α : Type u} (t : tactic α) : tactic (Sum α Stringₓ) := fun s =>
  match t s with
  | interaction_monad.result.success a s' => result.success (Sum.inl a) s
  | interaction_monad.result.exception msg' _ s' => result.success (Sum.inr (msg'.iget ()).toString) s

/-- Applies tactic `t`. If it succeeds, return the value. If it fails, returns the error message. -/
unsafe def try_or_report_error {α : Type u} (t : tactic α) : tactic (Sum α Stringₓ) := fun s =>
  match t s with
  | interaction_monad.result.success a s' => result.success (Sum.inl a) s'
  | interaction_monad.result.exception msg' _ s' => result.success (Sum.inr (msg'.iget ()).toString) s

/-- This tactic succeeds if `t` succeeds or fails with message `msg` such that `p msg` is `tt`.
-/
unsafe def succeeds_or_fails_with_msg {α : Type} (t : tactic α) (p : Stringₓ → Bool) : tactic Unit := do
  let x ← retrieve_or_report_error t
  match x with
    | Sum.inl _ => skip
    | Sum.inr msg => if p msg then skip else fail msg

add_tactic_doc
  { Name := "setup_tactic_parser", category := DocCategory.cmd, declNames := [`tactic.setup_tactic_parser_cmd],
    tags := ["parsing", "notation"] }

/-- `trace_error msg t` executes the tactic `t`. If `t` fails, traces `msg` and the failure message
of `t`. -/
unsafe def trace_error (msg : Stringₓ) (t : tactic α) : tactic α
  | s =>
    match t s with
    | result.success r s' => result.success r s'
    | result.exception (some msg') p s' => ((trace msg >> trace (msg' ())) >> result.exception (some msg') p) s'
    | result.exception none p s' => result.exception none p s'

/-- ``trace_if_enabled `n msg`` traces the message `msg`
only if tracing is enabled for the name `n`.

Create new names registered for tracing with `declare_trace n`.
Then use `set_option trace.n true/false` to enable or disable tracing for `n`.
-/
unsafe def trace_if_enabled (n : Name) {α : Type u} [has_to_tactic_format α] (msg : α) : tactic Unit :=
  when_tracing n (trace msg)

/-- ``trace_state_if_enabled `n msg`` prints the tactic state,
preceded by the optional string `msg`,
only if tracing is enabled for the name `n`.
-/
unsafe def trace_state_if_enabled (n : Name) (msg : Stringₓ := "") : tactic Unit :=
  when_tracing n ((if msg = "" then skip else trace msg) >> trace_state)

/-- This combinator is for testing purposes. It succeeds if `t` fails with message `msg`,
and fails otherwise.
-/
unsafe def success_if_fail_with_msg {α : Type u} (t : tactic α) (msg : Stringₓ) : tactic Unit := fun s =>
  match t s with
  | interaction_monad.result.exception msg' _ s' =>
    let expected_msg := (msg'.iget ()).toString
    if msg = expected_msg then result.success () s
    else
      mk_exception
        (f! "failure messages didn't match. Expected:
          {expected_msg}")
        none s
  | interaction_monad.result.success a s =>
    mk_exception "success_if_fail_with_msg combinator failed, given tactic succeeded" none s

/-- Construct a `Try this: refine ...` or `Try this: exact ...` string which would construct `g`.
-/
unsafe def tactic_statement (g : expr) : tactic Stringₓ := do
  let g ← instantiate_mvars g
  let g ← head_beta g
  let r ← pp (replace_mvars g)
  if g then return s! "Try this: refine {r}" else return s! "Try this: exact {r}"

/-- `with_local_goals gs tac` runs `tac` on the goals `gs` and then restores the
initial goals and returns the goals `tac` ended on. -/
unsafe def with_local_goals {α} (gs : List expr) (tac : tactic α) : tactic (α × List expr) := do
  let gs' ← get_goals
  set_goals gs
  finally (Prod.mk <$> tac <*> get_goals) (set_goals gs')

/-- like `with_local_goals` but discards the resulting goals -/
unsafe def with_local_goals' {α} (gs : List expr) (tac : tactic α) : tactic α :=
  Prod.fst <$> with_local_goals gs tac

/-- Representation of a proof goal that lends itself to comparison. The
following goal:

```lean
l₀ : T,
l₁ : T
⊢ ∀ v : T, foo
```

is represented as

```
(2, ∀ l₀ l₁ v : T, foo)
```

The number 2 indicates that first the two bound variables of the
`∀` are actually local constant. Comparing two such goals with `=`
rather than `=ₐ` or `is_def_eq` tells us that proof script should
not see the difference between the two.
 -/
unsafe def packaged_goal :=
  ℕ × expr

/-- proof state made of multiple `goal` meant for comparing
the result of running different tactics -/
unsafe def proof_state :=
  List packaged_goal

unsafe instance goal.inhabited : Inhabited packaged_goal :=
  ⟨(0, var 0)⟩

unsafe instance proof_state.inhabited : Inhabited proof_state :=
  (inferInstance : Inhabited (List packaged_goal))

/-- create a `packaged_goal` corresponding to the current goal -/
unsafe def get_packaged_goal : tactic packaged_goal := do
  let ls ← local_context
  let tgt ← target >>= instantiate_mvars
  let tgt ← pis ls tgt
  pure (ls, tgt)

/-- `goal_of_mvar g`, with `g` a meta variable, creates a
`packaged_goal` corresponding to `g` interpretted as a proof goal -/
unsafe def goal_of_mvar (g : expr) : tactic packaged_goal :=
  with_local_goals' [g] get_packaged_goal

/-- `get_proof_state` lists the user visible goal for each goal
of the current state and for each goal, abstracts all of the
meta variables of the other gaols.

This produces a list of goals in the form of `ℕ × expr` where
the `expr` encodes the following proof state:

```lean
2 goals
l₁ : t₁,
l₂ : t₂,
l₃ : t₃
⊢ tgt₁

⊢ tgt₂
```

as

```lean
[ (3, ∀ (mv : tgt₁) (mv : tgt₂) (l₁ : t₁) (l₂ : t₂) (l₃ : t₃), tgt₁),
  (0, ∀ (mv : tgt₁) (mv : tgt₂), tgt₂) ]
```

with 2 goals, the first 2 bound variables encode the meta variable
of all the goals, the next 3 (in the first goal) and 0 (in the second goal)
are the local constants.

This representation allows us to compare goals and proof states while
ignoring information like the unique name of local constants and
the equality or difference of meta variables that encode the same goal.
-/
unsafe def get_proof_state : tactic proof_state := do
  let gs ← get_goals
  gs fun g => do
      let ⟨n, g⟩ ← goal_of_mvar g
      let g ←
        gs
            (fun g v => do
              let g ← kabstract g v reducible ff
              pure <| pi `goal BinderInfo.default (quote.1 True) g)
            g
      pure (n, g)

/-- Run `tac` in a disposable proof state and return the state.
See `proof_state`, `goal` and `get_proof_state`.
-/
unsafe def get_proof_state_after (tac : tactic Unit) : tactic (Option proof_state) :=
  try_core <| retrieve <| tac >> get_proof_state

open Lean _Root_.Interactive

/-- A type alias for `tactic format`, standing for "pretty print format". -/
unsafe def pformat :=
  tactic format

/-- `mk` lifts `fmt : format` to the tactic monad (`pformat`). -/
unsafe def pformat.mk (fmt : format) : pformat :=
  pure fmt

/-- an alias for `pp`. -/
unsafe def to_pfmt {α} [has_to_tactic_format α] (x : α) : pformat :=
  pp x

unsafe instance pformat.has_to_tactic_format : has_to_tactic_format pformat :=
  ⟨id⟩

unsafe instance : Append pformat :=
  ⟨fun x y => (· ++ ·) <$> x <*> y⟩

unsafe instance tactic.has_to_tactic_format [has_to_tactic_format α] : has_to_tactic_format (tactic α) :=
  ⟨fun x => x >>= to_pfmt⟩

private unsafe def parse_pformat : Stringₓ → List Charₓ → parser pexpr
  | Acc, [] => pure (pquote.1 (to_pfmt (%%ₓreflect Acc)))
  | Acc, '\n' :: s => do
    let f ← parse_pformat "" s
    pure (pquote.1 (to_pfmt (%%ₓreflect Acc) ++ pformat.mk format.line ++ %%ₓf))
  | Acc, '{' :: '{' :: s => parse_pformat (Acc ++ "{") s
  | Acc, '{' :: s => do
    let (e, s) ← with_input (lean.parser.pexpr 0) s.asString
    let '}' :: s ← return s.toList | fail "'}' expected"
    let f ← parse_pformat "" s
    pure (pquote.1 (to_pfmt (%%ₓreflect Acc) ++ to_pfmt (%%ₓe) ++ %%ₓf))
  | Acc, c :: s => parse_pformat (Acc.str c) s

/-- See `format!` in `init/meta/interactive_base.lean`.

The main differences are that `pp` is called instead of `to_fmt` and that we can use
arguments of type `tactic α` in the quotations.

Now, consider the following:
```lean
e ← to_expr ``(3 + 7),
trace format!"{e}"  -- outputs `has_add.add.{0} nat nat.has_add
                    -- (bit1.{0} nat nat.has_one nat.has_add (has_one.one.{0} nat nat.has_one)) ...`
trace pformat!"{e}" -- outputs `3 + 7`
```

The difference is significant. And now, the following is expressible:

```lean
e ← to_expr ``(3 + 7),
trace pformat!"{e} : {infer_type e}" -- outputs `3 + 7 : ℕ`
```

See also: `trace!` and `fail!`
-/
@[user_notation]
unsafe def pformat_macro (_ : parse <| tk "pformat!") (s : Stringₓ) : parser pexpr := do
  let e ← parse_pformat "" s.toList
  return (pquote.1 (%%ₓe : pformat))

/-- The combination of `pformat` and `fail`.
-/
@[user_notation]
unsafe def fail_macro (_ : parse <| tk "fail!") (s : Stringₓ) : parser pexpr := do
  let e ← pformat_macro () s
  pure (pquote.1 ((%%ₓe : pformat) >>= fail))

/-- The combination of `pformat` and `trace`.
-/
@[user_notation]
unsafe def trace_macro (_ : parse <| tk "trace!") (s : Stringₓ) : parser pexpr := do
  let e ← pformat_macro () s
  pure (pquote.1 ((%%ₓe : pformat) >>= trace))

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- A hackish way to get the `src` directory of any project.
  Requires as argument any declaration name `n` in that project, and `k`, the number of characters
  in the path of the file where `n` is declared not part of the `src` directory.
  Example: For `mathlib_dir_locator` this is the length of `tactic/project_dir.lean`, so `23`.
  Note: does not work in the file where `n` is declared. -/
unsafe def get_project_dir (n : Name) (k : ℕ) : tactic Stringₓ := do
  let e ← get_env
  let s ←
    e.decl_olean n <|>
        "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
  return <| s k

/-- A hackish way to get the `src` directory of mathlib. -/
unsafe def get_mathlib_dir : tactic Stringₓ :=
  get_project_dir `mathlib_dir_locator 23

/-- Checks whether a declaration with the given name is declared in mathlib.
If you want to run this tactic many times, you should use `environment.is_prefix_of_file` instead,
since it is expensive to execute `get_mathlib_dir` many times. -/
unsafe def is_in_mathlib (n : Name) : tactic Bool := do
  let ml ← get_mathlib_dir
  let e ← get_env
  return <| e ml n

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Runs a tactic by name.
If it is a `tactic string`, return whatever string it returns.
If it is a `tactic unit`, return the name.
(This is mostly used in invoking "self-reporting tactics", e.g. by `tidy` and `hint`.)
-/
unsafe def name_to_tactic (n : Name) : tactic Stringₓ := do
  let d ← get_decl n
  let e ← mk_const n
  let t := d.type
  if expr.alpha_eqv t (quote.1 (tactic Unit)) then
      eval_expr (tactic Unit) e >>= fun t => t >> Name.toString <$> strip_prefix n
    else
      if expr.alpha_eqv t (quote.1 (tactic Stringₓ)) then eval_expr (tactic Stringₓ) e >>= fun t => t
      else
        "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"

/-- auxiliary function for `apply_under_n_pis` -/
private unsafe def apply_under_n_pis_aux (func arg : pexpr) : ℕ → ℕ → expr → pexpr
  | n, 0, _ =>
    let vars := (List.range n).reverse.map (@expr.var false)
    let bd := vars.foldl expr.app arg.mk_explicit
    func bd
  | n, k + 1, expr.pi nm bi tp bd => expr.pi nm bi (pexpr.of_expr tp) (apply_under_n_pis_aux (n + 1) k bd)
  | n, k + 1, t => apply_under_n_pis_aux n 0 t

/-- Assumes `pi_expr` is of the form `Π x1 ... xn xn+1..., _`.
Creates a pexpr of the form `Π x1 ... xn, func (arg x1 ... xn)`.
All arguments (implicit and explicit) to `arg` should be supplied. -/
unsafe def apply_under_n_pis (func arg : pexpr) (pi_expr : expr) (n : ℕ) : pexpr :=
  apply_under_n_pis_aux func arg 0 n pi_expr

/-- Assumes `pi_expr` is of the form `Π x1 ... xn, _`.
Creates a pexpr of the form `Π x1 ... xn, func (arg x1 ... xn)`.
All arguments (implicit and explicit) to `arg` should be supplied. -/
unsafe def apply_under_pis (func arg : pexpr) (pi_expr : expr) : pexpr :=
  apply_under_n_pis func arg pi_expr pi_expr.pi_arity

/-- If `func` is a `pexpr` representing a function that takes an argument `a`,
`get_pexpr_arg_arity_with_tgt func tgt` returns the arity of `a`.
When `tgt` is a `pi` expr, `func` is elaborated in a context
with the domain of `tgt`.

Examples:
* ```get_pexpr_arg_arity ``(ring) `(true)``` returns 0, since `ring` takes one non-function
  argument.
* ```get_pexpr_arg_arity_with_tgt ``(monad) `(true)``` returns 1, since `monad` takes one argument
  of type `α → α`.
* ```get_pexpr_arg_arity_with_tgt ``(module R) `(Π (R : Type), comm_ring R → true)``` returns 0
-/
unsafe def get_pexpr_arg_arity_with_tgt (func : pexpr) (tgt : expr) : tactic ℕ :=
  lock_tactic_state <| do
    let mv ← mk_mvar
    solve_aux tgt <| intros >> to_expr (pquote.1 ((%%ₓfunc) (%%ₓmv)))
    expr.pi_arity <$> (infer_type mv >>= instantiate_mvars)

/-- `find_private_decl n none` finds a private declaration named `n` in any of the imported files.

`find_private_decl n (some m)` finds a private declaration named `n` in the same file where a
declaration named `m` can be found. -/
unsafe def find_private_decl (n : Name) (fr : Option Name) : tactic Name := do
  let env ← get_env
  let fn ←
    OptionTₓ.run do
        let fr ← OptionTₓ.mk (return fr)
        let d ← monad_lift <| get_decl fr
        OptionTₓ.mk (return <| env d)
  let p : Stringₓ → Bool :=
    match fn with
    | some fn => fun x => fn = x
    | none => fun _ => true
  let xs :=
    env.decl_filter_map fun d => do
      let fn ← env.decl_olean d.to_name
      guardₓ (`_private.isPrefixOf d ∧ p fn ∧ d Name.anonymous = n)
      pure d
  match xs with
    | [n] => pure n
    | [] => fail "no such private found"
    | _ => fail "many matches found"

open Lean.Parser Interactive

/-- `import_private foo from bar` finds a private declaration `foo` in the same file as `bar`
and creates a local notation to refer to it.

`import_private foo` looks for `foo` in all imported files.

When possible, make `foo` non-private rather than using this feature.
 -/
@[user_command]
unsafe def import_private_cmd (_ : parse <| tk "import_private") : lean.parser Unit := do
  let n ← ident
  let fr ← optionalₓ (tk "from" *> ident)
  let n ← find_private_decl n fr
  let c ← resolve_constant n
  let d ← get_decl n
  let c := @expr.const true c d.univ_levels
  let new_n ← new_aux_decl_name
  add_decl <| declaration.defn new_n d d c ReducibilityHints.abbrev d
  let new_not := s!"local notation `{(n.updatePrefix Name.anonymous)}` := {new_n}"
  emit_command_here <| new_not
  skip

add_tactic_doc
  { Name := "import_private", category := DocCategory.cmd, declNames := [`tactic.import_private_cmd],
    tags := ["renaming"] }

/-- The command `mk_simp_attribute simp_name "description"` creates a simp set with name `simp_name`.
Lemmas tagged with `@[simp_name]` will be included when `simp with simp_name` is called.
`mk_simp_attribute simp_name none` will use a default description.

Appending the command with `with attr1 attr2 ...` will include all declarations tagged with
`attr1`, `attr2`, ... in the new simp set.

This command is preferred to using ``run_cmd mk_simp_attr `simp_name`` since it adds a doc string
to the attribute that is defined. If you need to create a simp set in a file where this command is
not available, you should use
```lean
run_cmd mk_simp_attr `simp_name
run_cmd add_doc_string `simp_attr.simp_name "Description of the simp set here"
```
-/
@[user_command]
unsafe def mk_simp_attribute_cmd (_ : parse <| tk "mk_simp_attribute") : lean.parser Unit := do
  let n ← ident
  let d ← parser.pexpr
  let d ← to_expr (pquote.1 (%%ₓd : Option Stringₓ))
  let descr ← eval_expr (Option Stringₓ) d
  let with_list ← tk "with" *> many ident <|> return []
  mk_simp_attr n with_list
  add_doc_string (name.append `simp_attr n) <| descr <| "simp set for " ++ toString n

add_tactic_doc
  { Name := "mk_simp_attribute", category := DocCategory.cmd, declNames := [`tactic.mk_simp_attribute_cmd],
    tags := ["simplification"] }

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Given a user attribute name `attr_name`, `get_user_attribute_name attr_name` returns
the name of the declaration that defines this attribute.
Fails if there is no user attribute with this name.
Example: ``get_user_attribute_name `norm_cast`` returns `` `norm_cast.norm_cast_attr`` -/
unsafe def get_user_attribute_name (attr_name : Name) : tactic Name := do
  let ns ← attribute.get_instances `user_attribute
  (ns fun nm => do
        let d ← get_decl nm
        let e ← mk_app `user_attribute.name [d]
        let attr_nm ← eval_expr Name e
        guardₓ <| attr_nm = attr_name
        return nm) <|>
      "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- A tactic to set either a basic attribute or a user attribute.
  If the user attribute has a parameter, the default value will be used.
  This tactic raises an error if there is no `inhabited` instance for the parameter type. -/
unsafe def set_attribute (attr_name : Name) (c_name : Name) (persistent := true) (prio : Option Nat := none) :
    tactic Unit := do
  get_decl c_name <|>
      "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
  let s ← try_or_report_error (set_basic_attribute attr_name c_name persistent prio)
  let Sum.inr msg ← return s | skip
  if msg = (f! "set_basic_attribute tactic failed, '{attr_name}' is not a basic attribute").toString then do
      let user_attr_nm ← get_user_attribute_name attr_name
      let user_attr_const ← mk_const user_attr_nm
      let tac ←
        eval_pexpr (tactic Unit)
              (pquote.1
                (user_attribute.set (%%ₓuser_attr_const) (%%ₓquote.1 c_name) default (%%ₓquote.1 persistent))) <|>
            "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
      tac
    else fail msg

end Tactic

/-- `find_defeq red m e` looks for a key in `m` that is defeq to `e` (up to transparency `red`),
and returns the value associated with this key if it exists.
Otherwise, it fails.
-/
unsafe def list.find_defeq (red : Tactic.Transparency) {v} (m : List (expr × v)) (e : expr) : tactic (expr × v) :=
  m.mfind fun ⟨e', val⟩ => tactic.is_def_eq e e' red

