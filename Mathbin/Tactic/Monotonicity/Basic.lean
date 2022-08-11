/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Order.BoundedOrder

namespace Tactic.Interactive

open Tactic List

open Lean Lean.Parser Interactive

open Interactive.Types

structure MonoCfg where
  unify := false
  deriving Inhabited

inductive MonoSelection : Type
  | left : mono_selection
  | right : mono_selection
  | both : mono_selection
  deriving DecidableEq, has_reflect, Inhabited

initialize
  registerTraceClass.1 `mono.relation

section Compare

parameter (opt : MonoCfg)

unsafe def compare (e₀ e₁ : expr) : tactic Unit := do
  if opt then do
      guardₓ (¬e₀ ∧ ¬e₁)
      unify e₀ e₁
    else is_def_eq e₀ e₁

unsafe def find_one_difference : List expr → List expr → tactic (List expr × expr × expr × List expr)
  | x :: xs, y :: ys => do
    let c ← try_core (compare x y)
    if c then Prod.map (cons x) id <$> find_one_difference xs ys
      else do
        guardₓ (xs = ys)
        mzipWith' compare xs ys
        return ([], x, y, xs)
  | xs, ys => fail f! "find_one_difference: {xs }, {ys}"

end Compare

def lastTwo {α : Type _} (l : List α) : Option (α × α) :=
  match l.reverse with
  | x₁ :: x₀ :: _ => some (x₀, x₁)
  | _ => none

unsafe def match_imp : expr → tactic (expr × expr)
  | quote.1 ((%%ₓe₀) → %%ₓe₁) => do
    guardₓ ¬e₁
    return (e₀, e₁)
  | _ => failed

open Expr

unsafe def same_operator : expr → expr → Bool
  | app e₀ _, app e₁ _ =>
    let fn₀ := e₀.get_app_fn
    let fn₁ := e₁.get_app_fn
    fn₀.is_constant ∧ fn₀.const_name = fn₁.const_name
  | pi _ _ _ _, pi _ _ _ _ => true
  | _, _ => false

unsafe def get_operator (e : expr) : Option Name :=
  (guardₓ ¬e.is_pi) >> pure e.get_app_fn.const_name

unsafe def monotonicity.check_rel (l r : expr) : tactic (Option Name) := do
  guardₓ (same_operator l r) <|> do
      fail f! "{l } and {r} should be the f x and f y for some f"
  if l then pure none else pure r

@[reducible]
def MonoKey :=
  WithBot Name × WithBot Name

unsafe instance mono_key.has_lt : LT MonoKey where lt := Prod.Lex (· < ·) (· < ·)

open Nat

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
unsafe def mono_head_candidates : ℕ → List expr → expr → tactic MonoKey
  | 0, _, h =>
    "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
  | succ n, xs, h =>
    (do
        let (rel, l, r) ←
          if h.is_arrow then pure (none, h.binding_domain, h.binding_body)
            else guardₓ h.get_app_fn.is_constant >> Prod.mk (some h.get_app_fn.const_name) <$> lastTwo h.get_app_args
        Prod.mk <$> monotonicity.check_rel l r <*> pure rel) <|>
      match xs with
      | [] => fail f! "oh? {h}"
      | x :: xs => mono_head_candidates n xs (h.pis [x])

unsafe def monotonicity.check (lm_n : Name) : tactic MonoKey := do
  let lm ← mk_const lm_n
  let lm_t ← infer_type lm >>= instantiate_mvars
  when_tracing `mono.relation
      (← do
        dbg_trace "[mono] Looking for relation in {← lm_t}")
  let s := simp_lemmas.mk
  let s ← s.add_simp `` Monotone
  let s ← s.add_simp `` StrictMono
  let lm_t ← s.dsimplify [] lm_t { failIfUnchanged := false }
  when_tracing `mono.relation
      (← do
        dbg_trace "[mono] Looking for relation in {← lm_t} (after unfolding)")
  let (xs, h) ← open_pis lm_t
  mono_head_candidates 3 xs h

unsafe instance : has_to_format MonoSelection :=
  ⟨fun x =>
    match x with
    | mono_selection.left => "left"
    | mono_selection.right => "right"
    | mono_selection.both => "both"⟩

unsafe def side : lean.parser MonoSelection :=
  with_desc "expecting 'left', 'right' or 'both' (default)" <| do
    let some n ← optionalₓ ident | pure MonoSelection.both
    if n = `left then pure <| mono_selection.left
      else
        if n = `right then pure <| mono_selection.right
        else
          if n = `both then pure <| mono_selection.both
          else fail f! "invalid argument: {n}, expecting 'left', 'right' or 'both' (default)"

open Function

@[user_attribute]
unsafe def monotonicity.attr : user_attribute (native.rb_lmap MonoKey Name) (Option MonoKey × mono_selection) where
  Name := `mono
  descr := "monotonicity of function `f` wrt relations `R₀` and `R₁`: R₀ x y → R₁ (f x) (f y)"
  cache_cfg :=
    { dependencies := [],
      mk_cache := fun ls => do
        let ps ← ls.mmap monotonicity.attr.get_param
        let ps := ps.filterMap Prod.fst
        pure <| (ps ls).foldl (flip <| uncurry fun k n m => m k n) (native.rb_lmap.mk mono_key _) }
  after_set :=
    some fun n prio p => do
      let (none, v) ← monotonicity.attr.get_param n | pure ()
      let k ← monotonicity.check n
      monotonicity.attr n (some k, v) p
  parser := Prod.mk none <$> side

unsafe def filter_instances (e : MonoSelection) (ns : List Name) : tactic (List Name) :=
  ns.mfilter fun n => do
    let d ← user_attribute.get_param_untyped monotonicity.attr n
    let (_, d) ← to_expr (pquote.1 (id (%%ₓd))) >>= eval_expr (Option MonoKey × mono_selection)
    return (e = d : Bool)

unsafe def get_monotonicity_lemmas (k : expr) (e : MonoSelection) : tactic (List Name) := do
  let ns ← monotonicity.attr.get_cache
  let k' ←
    if k.is_pi then pure (get_operator k.binding_domain, none)
      else do
        let (x₀, x₁) ← lastTwo k.get_app_args
        pure (get_operator x₀, some k)
  let ns := ns.find_def [] k'
  let ns' ← filter_instances e ns
  if e ≠ mono_selection.both then (· ++ ·) ns' <$> filter_instances mono_selection.both ns else pure ns'

end Tactic.Interactive

