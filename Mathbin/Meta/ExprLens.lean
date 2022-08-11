/-
Copyright (c) 2020 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Keeley Hoek, Scott Morrison
-/
import Mathbin.Data.List.Defs
import Mathbin.Tactic.DeriveInhabited

/-!
# A lens for zooming into nested `expr` applications

A "lens" for looking into the subterms of an expression, tracking where we've been, so that
when we "zoom out" after making a change we know exactly which order of `congr_fun`s and
`congr_arg`s we need to make things work.

This file defines the `expr_lens` inductive type, defines basic operations this type, and defines a
useful map-like function `expr.app_map` on `expr`s which maps over applications.

This file is for non-tactics.

## Tags

expr, expr_lens, congr, environment, meta, metaprogramming, tactic
-/


/-! ### Declarations about `expr_lens` -/


/-- You're supposed to think of an `expr_lens` as a big set of nested applications with a single
hole which needs to be filled, either in a function spot or argument spot. `expr_lens.fill` can
fill this hole and turn your lens back into a real `expr`. -/
unsafe inductive expr_lens
  | app_fun : expr_lens → expr → expr_lens
  | app_arg : expr_lens → expr → expr_lens
  | entire : expr_lens

namespace ExprLens

/-- Inductive type with two constructors `F` and `A`,
that represent the function-part `f` and arg-part `a` of an application `f a`. They specify the
directions in which an `expr_lens` should zoom into an `expr`.

This type is used in the development of rewriting tactics such as `nth_rewrite` and
`rewrite_search`. -/
inductive Dir
  | F
  | A
  deriving DecidableEq, Inhabited

/-- String representation of `dir`. -/
def Dir.toString : Dir → Stringₓ
  | dir.F => "F"
  | dir.A => "A"

instance : HasToString Dir :=
  ⟨Dir.toString⟩

open Tactic

/-- Fill the function or argument hole in this lens with the given `expr`. -/
unsafe def fill : expr_lens → expr → expr
  | entire, e => e
  | app_fun l f, x => l.fill (expr.app f x)
  | app_arg l x, f => l.fill (expr.app f x)

/-- Zoom into `e : expr` given the context of an `expr_lens`, popping out an `expr` and a new
zoomed `expr_lens`, if this is possible (`e` has to be an application). -/
unsafe def zoom : expr_lens → List Dir → expr → Option (expr_lens × expr)
  | l, [], e => (l, e)
  | l, dir.F :: rest, expr.app f x => (expr_lens.app_arg l x).zoom rest f
  | l, dir.A :: rest, expr.app f x => (expr_lens.app_fun l f).zoom rest x
  | _, _, _ => none

/-- Convert an `expr_lens` into a list of instructions needed to build it; repeatedly inspecting a
function or its argument a finite number of times. -/
unsafe def to_dirs : expr_lens → List Dir
  | expr_lens.entire => []
  | expr_lens.app_fun l _ => l.to_dirs.concat Dir.A
  | expr_lens.app_arg l _ => l.to_dirs.concat Dir.F

/-- Sometimes `mk_congr_arg` fails, when the function is 'superficially dependent'.
Try to `dsimp` the function first before building the `congr_arg` expression. -/
unsafe def mk_congr_arg_using_dsimp (G W : expr) (u : List Name) : tactic expr := do
  let s ← simp_lemmas.mk_default
  let t ← infer_type G
  let t' ← s.dsimplify u t { failIfUnchanged := false }
  to_expr (ppquote.1 (congr_arg (show %%ₓt' from %%ₓG) (%%ₓW)))

private unsafe def trace_congr_error (f : expr) (x_eq : expr) : tactic Unit := do
  let pp_f ← pp f
  let pp_f_t ← infer_type f >>= fun t => pp t
  let pp_x_eq ← pp x_eq
  let pp_x_eq_t ← infer_type x_eq >>= fun t => pp t
  trace
      f! "expr_lens.congr failed on 
        {pp_f } : {pp_f_t }
        {pp_x_eq } : {pp_x_eq_t}"

/-- Turn an `e : expr_lens` and a proof that `a = b` into a series of `congr_arg` or `congr_fun`
applications showing that the expressions obtained from `e.fill a` and `e.fill b` are equal. -/
unsafe def congr : expr_lens → expr → tactic expr
  | entire, e_eq => pure e_eq
  | app_fun l f, x_eq => do
    let fx_eq ←
      try_core <| do
          mk_congr_arg f x_eq <|> mk_congr_arg_using_dsimp f x_eq [`has_coe_to_fun.F]
    match fx_eq with
      | some fx_eq => l fx_eq
      | none => trace_congr_error f x_eq >> failed
  | app_arg l x, f_eq => mk_congr_fun f_eq x >>= l.congr

/-- Pretty print a lens. -/
unsafe def to_tactic_string : expr_lens → tactic Stringₓ
  | entire => return "(entire)"
  | app_fun l f => do
    let pp ← pp f
    let rest ← l.to_tactic_string
    return s! "(fun "{pp }" {rest})"
  | app_arg l x => do
    let pp ← pp x
    let rest ← l.to_tactic_string
    return s! "(arg "{pp }" {rest})"

end ExprLens

namespace Expr

/-- The private internal function used by `app_map`, which "does the work". -/
private unsafe def app_map_aux {α} (F : expr_lens → expr → tactic (List α)) :
    Option (expr_lens × expr) → tactic (List α)
  | some (l, e) =>
    List.join <$>
        Monadₓ.sequence [F l e, app_map_aux <| l.zoom [ExprLens.Dir.F] e, app_map_aux <| l.zoom [ExprLens.Dir.A] e] <|>
      pure []
  | none => pure []

/-- `app_map F e` maps a function `F` which understands `expr_lens`es
over the given `e : expr` in the natural way;
that is, make holes in `e` everywhere where that is possible
(generating `expr_lens`es in the process),
and at each stage call the function `F` passing
both the `expr_lens` generated and the `expr` which was removed to make the hole.

At each stage `F` returns a list of some type, and `app_map` collects these lists together and
returns a concatenation of them all. -/
unsafe def app_map {α} (F : expr_lens → expr → tactic (List α)) (e : expr) : tactic (List α) :=
  app_map_aux F (expr_lens.entire, e)

end Expr

