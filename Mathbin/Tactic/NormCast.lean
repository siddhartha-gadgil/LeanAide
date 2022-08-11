/-
Copyright (c) 2019 Paul-Nicolas Madelaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Nicolas Madelaine, Robert Y. Lewis
-/
import Mathbin.Tactic.Converter.Interactive
import Mathbin.Tactic.Hint

/-!
# A tactic for normalizing casts inside expressions

This tactic normalizes casts inside expressions.
It can be thought of as a call to the simplifier with a specific set of lemmas to
move casts upwards in the expression.
It has special handling of numerals and a simple heuristic to help moving
casts "past" binary operators.
Contrary to simp, it should be safe to use as a non-terminating tactic.

The algorithm implemented here is described in the paper
<https://lean-forward.github.io/norm_cast/norm_cast.pdf>.

## Important definitions
* `tactic.interactive.norm_cast`
* `tactic.interactive.push_cast`
* `tactic.interactive.exact_mod_cast`
* `tactic.interactive.apply_mod_cast`
* `tactic.interactive.rw_mod_cast`
* `tactic.interactive.assumption_mod_cast`
-/


setup_tactic_parser

namespace Tactic

/-- Runs `mk_instance` with a time limit.

This is a work around to the fact that in some cases
mk_instance times out instead of failing,
for example: `has_lift_t ℤ ℕ`

`mk_instance_fast` is used when we assume the type class search
should end instantly.
-/
unsafe def mk_instance_fast (e : expr) (timeout := 1000) : tactic expr :=
  try_for timeout (mk_instance e)

end Tactic

namespace NormCast

open Tactic Expr

initialize
  registerTraceClass.1 `norm_cast

/-- Output a trace message if `trace.norm_cast` is enabled.
-/
unsafe def trace_norm_cast {α} [has_to_tactic_format α] (msg : Stringₓ) (a : α) : tactic Unit :=
  when_tracing `norm_cast <| do
    let a ← pp a
    trace ("[norm_cast] " ++ msg ++ a : format)

mk_simp_attribute push_cast :=
  "The `push_cast` simp attribute uses `norm_cast` lemmas\nto move casts toward the leaf nodes of the expression."

/-- `label` is a type used to classify `norm_cast` lemmas.
* elim lemma:   LHS has 0 head coes and ≥ 1 internal coe
* move lemma:   LHS has 1 head coe and 0 internal coes,    RHS has 0 head coes and ≥ 1 internal coes
* squash lemma: LHS has ≥ 1 head coes and 0 internal coes, RHS has fewer head coes
-/
inductive Label
  | elim : label
  | move : label
  | squash : label
  deriving DecidableEq, has_reflect, Inhabited

namespace Label

/-- Convert `label` into `string`. -/
protected def toString : Label → Stringₓ
  | elim => "elim"
  | move => "move"
  | squash => "squash"

instance : HasToString Label :=
  ⟨Label.toString⟩

instance : HasRepr Label :=
  ⟨Label.toString⟩

unsafe instance : has_to_format Label :=
  ⟨fun l => l.toString⟩

/-- Convert `string` into `label`. -/
def ofString : Stringₓ → Option Label
  | "elim" => some elim
  | "move" => some move
  | "squash" => some squash
  | _ => none

end Label

open Label

/-- Count how many coercions are at the top of the expression. -/
unsafe def count_head_coes : expr → ℕ
  | quote.1 (coe (%%ₓe)) => count_head_coes e + 1
  | quote.1 (coeSort (%%ₓe)) => count_head_coes e + 1
  | quote.1 (coeFn (%%ₓe)) => count_head_coes e + 1
  | _ => 0

/-- Count how many coercions are inside the expression, including the top ones. -/
unsafe def count_coes : expr → tactic ℕ
  | quote.1 (coe (%%ₓe)) => (· + 1) <$> count_coes e
  | quote.1 (coeSort (%%ₓe)) => (· + 1) <$> count_coes e
  | quote.1 (coeFn (%%ₓe)) => (· + 1) <$> count_coes e
  | app (quote.1 (coeFn (%%ₓe))) x => (· + ·) <$> count_coes x <*> (· + 1) <$> count_coes e
  | expr.lam n bi t e => do
    let l ← mk_local' n bi t
    count_coes <| e l
  | e => do
    let as ← e.get_simp_args
    List.sum <$> as count_coes

/-- Count how many coercions are inside the expression, excluding the top ones. -/
private unsafe def count_internal_coes (e : expr) : tactic ℕ := do
  let ncoes ← count_coes e
  pure <| ncoes - count_head_coes e

/-- Classifies a declaration of type `ty` as a `norm_cast` rule.
-/
unsafe def classify_type (ty : expr) : tactic Label := do
  let (_, ty) ← open_pis ty
  let (lhs, rhs) ←
    match ty with
      | quote.1 ((%%ₓlhs) = %%ₓrhs) => pure (lhs, rhs)
      | quote.1 ((%%ₓlhs) ↔ %%ₓrhs) => pure (lhs, rhs)
      | _ => fail "norm_cast: lemma must be = or ↔"
  let lhs_coes ← count_coes lhs
  when (lhs_coes = 0) <| fail "norm_cast: badly shaped lemma, lhs must contain at least one coe"
  let lhs_head_coes := count_head_coes lhs
  let lhs_internal_coes ← count_internal_coes lhs
  let rhs_head_coes := count_head_coes rhs
  let rhs_internal_coes ← count_internal_coes rhs
  if lhs_head_coes = 0 then return elim
    else
      if lhs_head_coes = 1 then do
        when (rhs_head_coes ≠ 0) <| fail "norm_cast: badly shaped lemma, rhs can't start with coe"
        if rhs_internal_coes = 0 then return squash else return move
      else
        if rhs_head_coes < lhs_head_coes then do
          return squash
        else do
          fail "norm_cast: badly shaped shaped squash lemma, rhs must have fewer head coes than lhs"

/-- The cache for `norm_cast` attribute stores three `simp_lemma` objects. -/
unsafe structure norm_cast_cache where
  up : simp_lemmas
  down : simp_lemmas
  squash : simp_lemmas

/-- Empty `norm_cast_cache`. -/
unsafe def empty_cache : norm_cast_cache where
  up := simp_lemmas.mk
  down := simp_lemmas.mk
  squash := simp_lemmas.mk

unsafe instance : Inhabited norm_cast_cache :=
  ⟨empty_cache⟩

/-- `add_elim cache e` adds `e` as an `elim` lemma to `cache`. -/
unsafe def add_elim (cache : norm_cast_cache) (e : expr) : tactic norm_cast_cache := do
  let new_up ← cache.up.add e
  return { up := new_up, down := cache, squash := cache }

/-- `add_move cache e` adds `e` as a `move` lemma to `cache`. -/
unsafe def add_move (cache : norm_cast_cache) (e : expr) : tactic norm_cast_cache := do
  let new_up ← cache.up.add e true
  let new_down ← cache.down.add e
  return { up := new_up, down := new_down, squash := cache }

/-- `add_squash cache e` adds `e` as an `squash` lemma to `cache`. -/
unsafe def add_squash (cache : norm_cast_cache) (e : expr) : tactic norm_cast_cache := do
  let new_squash ← cache.squash.add e
  let new_down ← cache.down.add e
  return { up := cache, down := new_down, squash := new_squash }

/-- The type of the `norm_cast` attribute.
The optional label is used to overwrite the classifier.
-/
unsafe def norm_cast_attr_ty : Type :=
  user_attribute norm_cast_cache (Option Label)

/-- Efficient getter for the `@[norm_cast]` attribute parameter that does not call `eval_expr`.

See Note [user attribute parameters].
-/
unsafe def get_label_param (attr : norm_cast_attr_ty) (decl : Name) : tactic (Option Label) := do
  let p ← attr.get_param_untyped decl
  match p with
    | quote.1 none => pure none
    | quote.1 (some Label.elim) => pure label.elim
    | quote.1 (some Label.move) => pure label.move
    | quote.1 (some Label.squash) => pure label.squash
    | _ => fail p

/-- `add_lemma cache decl` infers the proper `norm_cast` attribute for `decl` and adds it to `cache`.
-/
unsafe def add_lemma (attr : norm_cast_attr_ty) (cache : norm_cast_cache) (decl : Name) : tactic norm_cast_cache := do
  let e ← mk_const decl
  let param ← get_label_param attr decl
  let l ← param <|> infer_type e >>= classify_type
  match l with
    | elim => add_elim cache e
    | move => add_move cache e
    | squash => add_squash cache e

-- special lemmas to handle the ≥, > and ≠ operators
private theorem ge_from_le {α} [LE α] : ∀ x y : α, x ≥ y ↔ y ≤ x := fun _ _ => Iff.rfl

private theorem gt_from_lt {α} [LT α] : ∀ x y : α, x > y ↔ y < x := fun _ _ => Iff.rfl

private theorem ne_from_not_eq {α} : ∀ x y : α, x ≠ y ↔ ¬x = y := fun _ _ => Iff.rfl

/-- `mk_cache names` creates a `norm_cast_cache`. It infers the proper `norm_cast` attributes
for names in `names`, and collects the lemmas attributed with specific `norm_cast` attributes.
-/
unsafe def mk_cache (attr : Thunkₓ norm_cast_attr_ty) (names : List Name) : tactic norm_cast_cache := do
  let cache
    ←-- names has the declarations in reverse order
          names.mfoldr
        (fun name cache => add_lemma (attr ()) cache Name) empty_cache
  let--some special lemmas to handle binary relations
  up := cache.up
  let up ← up.add_simp `` ge_from_le
  let up ← up.add_simp `` gt_from_lt
  let up ← up.add_simp `` ne_from_not_eq
  let down := cache.down
  let down ← down.add_simp `` coe_coe
  pure { up, down, squash := cache }

/-- The `norm_cast` attribute.
-/
@[user_attribute]
unsafe def norm_cast_attr : user_attribute norm_cast_cache (Option Label) where
  Name := `norm_cast
  descr := "attribute for norm_cast"
  parser :=
    (do
        let some l ← (label.of_string ∘ toString) <$> ident
        return l) <|>
      return none
  after_set :=
    some fun decl prio persistent => do
      let param ← get_label_param norm_cast_attr decl
      match param with
        | some l => when (l ≠ elim) <| simp_attr.push_cast decl () tt prio
        | none => do
          let e ← mk_const decl
          let ty ← infer_type e
          let l ← classify_type ty
          norm_cast_attr decl l persistent prio
  before_unset := some fun _ _ => tactic.skip
  cache_cfg := { mk_cache := mk_cache norm_cast_attr, dependencies := [] }

/-- Classify a declaration as a `norm_cast` rule. -/
unsafe def make_guess (decl : Name) : tactic Label := do
  let e ← mk_const decl
  let ty ← infer_type e
  classify_type ty

/-- Gets the `norm_cast` classification label for a declaration. Applies the
override specified on the attribute, if necessary.
-/
unsafe def get_label (decl : Name) : tactic Label := do
  let param ← get_label_param norm_cast_attr decl
  param <|> make_guess decl

end NormCast

namespace Tactic.Interactive

open NormCast

/-- `push_cast` rewrites the expression to move casts toward the leaf nodes.
For example, `↑(a + b)` will be written to `↑a + ↑b`.
Equivalent to `simp only with push_cast`.
Can also be used at hypotheses.

`push_cast` can also be used at hypotheses and with extra simp rules.

```lean
example (a b : ℕ) (h1 : ((a + b : ℕ) : ℤ) = 10) (h2 : ((a + b + 0 : ℕ) : ℤ) = 10) :
  ((a + b : ℕ) : ℤ) = 10 :=
begin
  push_cast,
  push_cast at h1,
  push_cast [int.add_zero] at h2,
end
```
-/
unsafe def push_cast (hs : parse tactic.simp_arg_list) (l : parse location) : tactic Unit :=
  tactic.interactive.simp none none true hs [`push_cast] l { discharger := tactic.assumption }

end Tactic.Interactive

namespace NormCast

open Tactic Expr

/-- Prove `a = b` using the given simp set. -/
unsafe def prove_eq_using (s : simp_lemmas) (a b : expr) : tactic expr := do
  let (a', a_a', _) ← simplify s [] a { failIfUnchanged := false }
  let (b', b_b', _) ← simplify s [] b { failIfUnchanged := false }
  on_exception (trace_norm_cast "failed: " (to_expr (pquote.1 ((%%ₓa') = %%ₓb')) >>= pp)) <| is_def_eq a' b' reducible
  let b'_b ← mk_eq_symm b_b'
  mk_eq_trans a_a' b'_b

/-- Prove `a = b` by simplifying using move and squash lemmas. -/
unsafe def prove_eq_using_down (a b : expr) : tactic expr := do
  let cache ← norm_cast_attr.get_cache
  trace_norm_cast "proving: " (to_expr (pquote.1 ((%%ₓa) = %%ₓb)) >>= pp)
  prove_eq_using cache a b

/-- This is the main heuristic used alongside the elim and move lemmas.
The goal is to help casts move past operators by adding intermediate casts.
An expression of the shape: op (↑(x : α) : γ) (↑(y : β) : γ)
is rewritten to:            op (↑(↑(x : α) : β) : γ) (↑(y : β) : γ)
when (↑(↑(x : α) : β) : γ) = (↑(x : α) : γ) can be proven with a squash lemma
-/
unsafe def splitting_procedure : expr → tactic (expr × expr)
  | app (app op x) y =>
    (do
        let quote.1 (@coe (%%ₓα) (%%ₓδ) (%%ₓcoe1) (%%ₓxx)) ← return x
        let quote.1 (@coe (%%ₓβ) (%%ₓγ) (%%ₓcoe2) (%%ₓyy)) ← return y
        success_if_fail <| is_def_eq α β
        is_def_eq δ γ
        (do
              let coe3 ← mk_app `has_lift_t [α, β] >>= mk_instance_fast
              let new_x ← to_expr (pquote.1 (@coe (%%ₓβ) (%%ₓδ) (%%ₓcoe2) (@coe (%%ₓα) (%%ₓβ) (%%ₓcoe3) (%%ₓxx))))
              let new_e := app (app op new_x) y
              let eq_x ← prove_eq_using_down x new_x
              let pr ← mk_congr_arg op eq_x
              let pr ← mk_congr_fun pr y
              return (new_e, pr)) <|>
            do
            let coe3 ← mk_app `has_lift_t [β, α] >>= mk_instance_fast
            let new_y ← to_expr (pquote.1 (@coe (%%ₓα) (%%ₓδ) (%%ₓcoe1) (@coe (%%ₓβ) (%%ₓα) (%%ₓcoe3) (%%ₓyy))))
            let new_e := app (app op x) new_y
            let eq_y ← prove_eq_using_down y new_y
            let pr ← mk_congr_arg (app op x) eq_y
            return (new_e, pr)) <|>
      (do
          let quote.1 (@coe (%%ₓα) (%%ₓβ) (%%ₓcoe1) (%%ₓxx)) ← return x
          let quote.1 (@One.one (%%ₓβ) (%%ₓh1)) ← return y
          let h2 ← to_expr (pquote.1 (One (%%ₓα))) >>= mk_instance_fast
          let new_y ← to_expr (pquote.1 (@coe (%%ₓα) (%%ₓβ) (%%ₓcoe1) (@One.one (%%ₓα) (%%ₓh2))))
          let eq_y ← prove_eq_using_down y new_y
          let new_e := app (app op x) new_y
          let pr ← mk_congr_arg (app op x) eq_y
          return (new_e, pr)) <|>
        (do
            let quote.1 (@coe (%%ₓα) (%%ₓβ) (%%ₓcoe1) (%%ₓxx)) ← return x
            let quote.1 (@Zero.zero (%%ₓβ) (%%ₓh1)) ← return y
            let h2 ← to_expr (pquote.1 (Zero (%%ₓα))) >>= mk_instance_fast
            let new_y ← to_expr (pquote.1 (@coe (%%ₓα) (%%ₓβ) (%%ₓcoe1) (@Zero.zero (%%ₓα) (%%ₓh2))))
            let eq_y ← prove_eq_using_down y new_y
            let new_e := app (app op x) new_y
            let pr ← mk_congr_arg (app op x) eq_y
            return (new_e, pr)) <|>
          (do
              let quote.1 (@One.one (%%ₓβ) (%%ₓh1)) ← return x
              let quote.1 (@coe (%%ₓα) (%%ₓβ) (%%ₓcoe1) (%%ₓxx)) ← return y
              let h1 ← to_expr (pquote.1 (One (%%ₓα))) >>= mk_instance_fast
              let new_x ← to_expr (pquote.1 (@coe (%%ₓα) (%%ₓβ) (%%ₓcoe1) (@One.one (%%ₓα) (%%ₓh1))))
              let eq_x ← prove_eq_using_down x new_x
              let new_e := app (app op new_x) y
              let pr ← mk_congr_arg (lam `x BinderInfo.default β (app (app op (var 0)) y)) eq_x
              return (new_e, pr)) <|>
            do
            let quote.1 (@Zero.zero (%%ₓβ) (%%ₓh1)) ← return x
            let quote.1 (@coe (%%ₓα) (%%ₓβ) (%%ₓcoe1) (%%ₓxx)) ← return y
            let h1 ← to_expr (pquote.1 (Zero (%%ₓα))) >>= mk_instance_fast
            let new_x ← to_expr (pquote.1 (@coe (%%ₓα) (%%ₓβ) (%%ₓcoe1) (@Zero.zero (%%ₓα) (%%ₓh1))))
            let eq_x ← prove_eq_using_down x new_x
            let new_e := app (app op new_x) y
            let pr ← mk_congr_arg (lam `x BinderInfo.default β (app (app op (var 0)) y)) eq_x
            return (new_e, pr)
  | _ => failed

/-- Discharging function used during simplification in the "squash" step.

TODO: norm_cast takes a list of expressions to use as lemmas for the discharger
TODO: a tactic to print the results the discharger fails to proove
-/
private unsafe def prove : tactic Unit :=
  assumption

/-- Core rewriting function used in the "squash" step, which moves casts upwards
and eliminates them.

It tries to rewrite an expression using the elim and move lemmas.
On failure, it calls the splitting procedure heuristic.
-/
unsafe def upward_and_elim (s : simp_lemmas) (e : expr) : tactic (expr × expr) :=
  (do
      let r ← mcond (is_prop e) (return `iff) (return `eq)
      let (new_e, pr) ← s.rewrite e prove r
      let pr ←
        match r with
          | `iff => mk_app `propext [pr]
          | _ => return pr
      return (new_e, pr)) <|>
    splitting_procedure e

/-!
The following auxiliary functions are used to handle numerals.
-/


/-- If possible, rewrite `(n : α)` to `((n : ℕ) : α)` where `n` is a numeral and `α ≠ ℕ`.
Returns a pair of the new expression and proof that they are equal.
-/
unsafe def numeral_to_coe (e : expr) : tactic (expr × expr) := do
  let α ← infer_type e
  success_if_fail <| is_def_eq α (quote.1 ℕ)
  let n ← e.toNat
  let h1 ← mk_app `has_lift_t [quote.1 ℕ, α] >>= mk_instance_fast
  let new_e : expr := reflect n
  let new_e ← to_expr (pquote.1 (@coe ℕ (%%ₓα) (%%ₓh1) (%%ₓnew_e)))
  let pr ← prove_eq_using_down e new_e
  return (new_e, pr)

/-- If possible, rewrite `((n : ℕ) : α)` to `(n : α)` where `n` is a numeral.
Returns a pair of the new expression and proof that they are equal.
-/
unsafe def coe_to_numeral (e : expr) : tactic (expr × expr) := do
  let quote.1 (@coe ℕ (%%ₓα) (%%ₓh1) (%%ₓe')) ← return e
  let n ← e'.toNat
  -- replace e' by normalized numeral
      is_def_eq
      (reflect n) e' reducible
  let e := e.app_fn (reflect n)
  let new_e ← expr.of_nat α n
  let pr ← prove_eq_using_down e new_e
  return (new_e, pr)

/-- A local variant on `simplify_top_down`. -/
private unsafe def simplify_top_down' {α} (a : α) (pre : α → expr → tactic (α × expr × expr)) (e : expr)
    (cfg : SimpConfig := {  }) : tactic (α × expr × expr) :=
  ext_simplify_core a cfg simp_lemmas.mk (fun _ => failed)
    (fun a _ _ _ e => do
      let (new_a, new_e, pr) ← pre a e
      guardₓ ¬expr.alpha_eqv new_e e
      return (new_a, new_e, some pr, ff))
    (fun _ _ _ _ _ => failed) `eq e

/-- The core simplification routine of `norm_cast`.
-/
unsafe def derive (e : expr) : tactic (expr × expr) := do
  let cache ← norm_cast_attr.get_cache
  let e ← instantiate_mvars e
  let cfg : SimpConfig :=
    { zeta := false, beta := false, eta := false, proj := false, iota := false, iotaEqn := false,
      failIfUnchanged := false }
  let e0 := e
  let-- step 1: pre-processing of numerals
    ((), e1, pr1)
    ← simplify_top_down' () (fun _ e => Prod.mk () <$> numeral_to_coe e) e0 cfg
  trace_norm_cast "after numeral_to_coe: " e1
  let-- step 2: casts are moved upwards and eliminated
    ((), e2, pr2)
    ← simplify_bottom_up () (fun _ e => Prod.mk () <$> upward_and_elim cache.up e) e1 cfg
  trace_norm_cast "after upward_and_elim: " e2
  let-- step 3: casts are squashed
    (e3, pr3, _)
    ← simplify cache.squash [] e2 cfg
  trace_norm_cast "after squashing: " e3
  let-- step 4: post-processing of numerals
    ((), e4, pr4)
    ← simplify_top_down' () (fun _ e => Prod.mk () <$> coe_to_numeral e) e3 cfg
  trace_norm_cast "after coe_to_numeral: " e4
  let new_e := e4
  guardₓ ¬expr.alpha_eqv new_e e
  let pr ← mk_eq_trans pr1 pr2
  let pr ← mk_eq_trans pr pr3
  let pr ← mk_eq_trans pr pr4
  return (new_e, pr)

/-- A small variant of `push_cast` suited for non-interactive use.

`derive_push_cast extra_lems e` returns an expression `e'` and a proof that `e = e'`.
-/
unsafe def derive_push_cast (extra_lems : List simp_arg_type) (e : expr) : tactic (expr × expr) := do
  let (s, _) ← mk_simp_set true [`push_cast] extra_lems
  let (e, prf, _) ← simplify (s.erase [`nat.cast_succ]) [] e { failIfUnchanged := false } `eq tactic.assumption
  return (e, prf)

end NormCast

namespace Tactic

open Expr NormCast

/-- `aux_mod_cast e` runs `norm_cast` on `e` and returns the result. If `include_goal` is true, it
also normalizes the goal. -/
unsafe def aux_mod_cast (e : expr) (include_goal : Bool := true) : tactic expr :=
  match e with
  | local_const _ lc _ _ => do
    let e ← get_local lc
    replace_at derive [e] include_goal
    get_local lc
  | e => do
    let t ← infer_type e
    let e ← assertv `this t e
    replace_at derive [e] include_goal
    get_local `this

/-- `exact_mod_cast e` runs `norm_cast` on the goal and `e`, and tries to use `e` to close the
goal. -/
unsafe def exact_mod_cast (e : expr) : tactic Unit :=
  decorate_error "exact_mod_cast failed:" <| do
    let new_e ← aux_mod_cast e
    exact new_e

/-- `apply_mod_cast e` runs `norm_cast` on the goal and `e`, and tries to apply `e`. -/
unsafe def apply_mod_cast (e : expr) : tactic (List (Name × expr)) :=
  decorate_error "apply_mod_cast failed:" <| do
    let new_e ← aux_mod_cast e
    apply new_e

/-- `assumption_mod_cast` runs `norm_cast` on the goal. For each local hypothesis `h`, it also
normalizes `h` and tries to use that to close the goal. -/
unsafe def assumption_mod_cast : tactic Unit :=
  decorate_error "assumption_mod_cast failed:" <| do
    let cfg : SimpConfig :=
      { failIfUnchanged := false, canonizeInstances := false, canonizeProofs := false, proj := false }
    replace_at derive [] tt
    let ctx ← local_context
    ctx fun h => aux_mod_cast h ff >>= tactic.exact

end Tactic

namespace Tactic.Interactive

open Tactic NormCast

/-- Normalize casts at the given locations by moving them "upwards".
As opposed to simp, norm_cast can be used without necessarily closing the goal.
-/
unsafe def norm_cast (loc : parse location) : tactic Unit := do
  let ns ← loc.get_locals
  let tt ← replace_at derive ns loc.include_goal | fail "norm_cast failed to simplify"
  when loc <| try tactic.reflexivity
  when loc <| try tactic.triv
  when ¬ns <| try tactic.contradiction

/-- Rewrite with the given rules and normalize casts between steps.
-/
unsafe def rw_mod_cast (rs : parse rw_rules) (loc : parse location) : tactic Unit :=
  decorate_error "rw_mod_cast failed:" <| do
    let cfg_norm : SimpConfig := {  }
    let cfg_rw : RewriteCfg := {  }
    let ns ← loc.get_locals
    Monadₓ.mapm'
        (fun r : rw_rule => do
          save_info r
          replace_at derive ns loc
          rw ⟨[r], none⟩ loc {  })
        rs
    replace_at derive ns loc
    skip

/-- Normalize the goal and the given expression, then close the goal with exact.
-/
unsafe def exact_mod_cast (e : parse texpr) : tactic Unit := do
  let e ←
    i_to_expr e <|> do
        let ty ← target
        let e ← i_to_expr_strict (pquote.1 (%%ₓe : %%ₓty))
        let pty ← pp ty
        let ptgt ← pp e
        fail
            ("exact_mod_cast failed, expression type not directly " ++
                    "inferrable. Try:\n\nexact_mod_cast ...\nshow " ++
                  to_fmt pty ++
                ",\nfrom " ++
              ptgt :
              format)
  tactic.exact_mod_cast e

/-- Normalize the goal and the given expression, then apply the expression to the goal.
-/
unsafe def apply_mod_cast (e : parse texpr) : tactic Unit := do
  let e ← i_to_expr_for_apply e
  concat_tags <| tactic.apply_mod_cast e

/-- Normalize the goal and every expression in the local context, then close the goal with assumption.
-/
unsafe def assumption_mod_cast : tactic Unit :=
  tactic.assumption_mod_cast

end Tactic.Interactive

namespace Conv.Interactive

open Conv

open NormCast (derive)

/-- the converter version of `norm_cast' -/
unsafe def norm_cast : conv Unit :=
  replace_lhs derive

end Conv.Interactive

-- TODO: move this elsewhere?
@[norm_cast]
theorem ite_cast {α β} [HasLiftT α β] {c : Prop} [Decidable c] {a b : α} : ↑(ite c a b) = ite c (↑a : β) (↑b : β) := by
  by_cases' h : c <;> simp [← h]

@[norm_cast]
theorem dite_cast {α β} [HasLiftT α β] {c : Prop} [Decidable c] {a : c → α} {b : ¬c → α} :
    ↑(dite c a b) = dite c (fun h => (↑(a h) : β)) fun h => (↑(b h) : β) := by
  by_cases' h : c <;> simp [← h]

add_hint_tactic norm_cast  at *

/-- The `norm_cast` family of tactics is used to normalize casts inside expressions.
It is basically a simp tactic with a specific set of lemmas to move casts
upwards in the expression.
Therefore it can be used more safely as a non-terminating tactic.
It also has special handling of numerals.

For instance, given an assumption
```lean
a b : ℤ
h : ↑a + ↑b < (10 : ℚ)
```

writing `norm_cast at h` will turn `h` into
```lean
h : a + b < 10
```

You can also use `exact_mod_cast`, `apply_mod_cast`, `rw_mod_cast`
or `assumption_mod_cast`.
Writing `exact_mod_cast h` and `apply_mod_cast h` will normalize the goal and
`h` before using `exact h` or `apply h`.
Writing `assumption_mod_cast` will normalize the goal and for every
expression `h` in the context it will try to normalize `h` and use
`exact h`.
`rw_mod_cast` acts like the `rw` tactic but it applies `norm_cast` between steps.

`push_cast` rewrites the expression to move casts toward the leaf nodes.
This uses `norm_cast` lemmas in the forward direction.
For example, `↑(a + b)` will be written to `↑a + ↑b`.
It is equivalent to `simp only with push_cast`.
It can also be used at hypotheses with `push_cast at h`
and with extra simp lemmas with `push_cast [int.add_zero]`.

```lean
example (a b : ℕ) (h1 : ((a + b : ℕ) : ℤ) = 10) (h2 : ((a + b + 0 : ℕ) : ℤ) = 10) :
  ((a + b : ℕ) : ℤ) = 10 :=
begin
  push_cast,
  push_cast at h1,
  push_cast [int.add_zero] at h2,
end
```

The implementation and behavior of the `norm_cast` family is described in detail at
<https://lean-forward.github.io/norm_cast/norm_cast.pdf>.
-/
add_tactic_doc
  { Name := "norm_cast", category := DocCategory.tactic,
    declNames :=
      [`` tactic.interactive.norm_cast, `` tactic.interactive.rw_mod_cast, `` tactic.interactive.apply_mod_cast,
        `` tactic.interactive.assumption_mod_cast, `` tactic.interactive.exact_mod_cast,
        `` tactic.interactive.push_cast],
    tags := ["coercions", "simplification"] }

/-- The `norm_cast` attribute should be given to lemmas that describe the
behaviour of a coercion in regard to an operator, a relation, or a particular
function.

It only concerns equality or iff lemmas involving `↑`, `⇑` and `↥`, describing the behavior of
the coercion functions.
It does not apply to the explicit functions that define the coercions.

Examples:
```lean
@[norm_cast] theorem coe_nat_inj' {m n : ℕ} : (↑m : ℤ) = ↑n ↔ m = n

@[norm_cast] theorem coe_int_denom (n : ℤ) : (n : ℚ).denom = 1

@[norm_cast] theorem cast_id : ∀ n : ℚ, ↑n = n

@[norm_cast] theorem coe_nat_add (m n : ℕ) : (↑(m + n) : ℤ) = ↑m + ↑n

@[norm_cast] theorem cast_sub [add_group α] [has_one α] {m n} (h : m ≤ n) :
  ((n - m : ℕ) : α) = n - m

@[norm_cast] theorem coe_nat_bit0 (n : ℕ) : (↑(bit0 n) : ℤ) = bit0 ↑n

@[norm_cast] theorem cast_coe_nat (n : ℕ) : ((n : ℤ) : α) = n

@[norm_cast] theorem cast_one : ((1 : ℚ) : α) = 1
```

Lemmas tagged with `@[norm_cast]` are classified into three categories: `move`, `elim`, and
`squash`. They are classified roughly as follows:

* elim lemma:   LHS has 0 head coes and ≥ 1 internal coe
* move lemma:   LHS has 1 head coe and 0 internal coes,    RHS has 0 head coes and ≥ 1 internal coes
* squash lemma: LHS has ≥ 1 head coes and 0 internal coes, RHS has fewer head coes

`norm_cast` uses `move` and `elim` lemmas to factor coercions toward the root of an expression
and to cancel them from both sides of an equation or relation. It uses `squash` lemmas to clean
up the result.

Occasionally you may want to override the automatic classification.
You can do this by giving an optional `elim`, `move`, or `squash` parameter to the attribute.

```lean
@[simp, norm_cast elim] lemma nat_cast_re (n : ℕ) : (n : ℂ).re = n :=
by rw [← of_real_nat_cast, of_real_re]
```

Don't do this unless you understand what you are doing.

A full description of the tactic, and the use of each lemma category, can be found at
<https://lean-forward.github.io/norm_cast/norm_cast.pdf>.
-/
add_tactic_doc
  { Name := "norm_cast attributes", category := DocCategory.attr, declNames := [`` norm_cast.norm_cast_attr],
    tags := ["coercions", "simplification"] }

