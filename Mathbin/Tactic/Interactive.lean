/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Sébastien Gouëzel, Scott Morrison
-/
import Mathbin.Logic.Nonempty
import Mathbin.Tactic.Lint.Default
import Mathbin.Tactic.Dependencies

setup_tactic_parser

namespace Tactic

namespace Interactive

open Interactive Interactive.Types Expr

/-- Similar to `constructor`, but does not reorder goals. -/
unsafe def fconstructor : tactic Unit :=
  concat_tags tactic.fconstructor

add_tactic_doc
  { Name := "fconstructor", category := DocCategory.tactic, declNames := [`tactic.interactive.fconstructor],
    tags := ["logic", "goal management"] }

/-- `try_for n { tac }` executes `tac` for `n` ticks, otherwise uses `sorry` to close the goal.
Never fails. Useful for debugging. -/
unsafe def try_for (max : parse parser.pexpr) (tac : itactic) : tactic Unit := do
  let max ← i_to_expr_strict max >>= tactic.eval_expr Nat
  fun s =>
    match _root_.try_for max (tac s) with
    | some r => r
    | none => (tactic.trace "try_for timeout, using sorry" >> tactic.admit) s

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr *»
/-- Multiple `subst`. `substs x y z` is the same as `subst x, subst y, subst z`. -/
unsafe def substs (l : parse («expr *» ident)) : tactic Unit :=
  propagate_tags <| (l.mmap' fun h => get_local h >>= tactic.subst) >> try (tactic.reflexivity reducible)

add_tactic_doc
  { Name := "substs", category := DocCategory.tactic, declNames := [`tactic.interactive.substs], tags := ["rewriting"] }

/-- Unfold coercion-related definitions -/
unsafe def unfold_coes (loc : parse location) : tactic Unit :=
  unfold
    [`` coe, `` coeT, `` CoeT.coeₓ, `` coeB, `` Coe.coe, `` lift, `` HasLift.lift, `` liftT, `` HasLiftT.lift, `` coeFn,
      `` CoeFun.coe, `` coeSort, `` CoeSort.coe]
    loc

add_tactic_doc
  { Name := "unfold_coes", category := DocCategory.tactic, declNames := [`tactic.interactive.unfold_coes],
    tags := ["simplification"] }

/-- Unfold `has_well_founded.r`, `sizeof` and other such definitions. -/
unsafe def unfold_wf :=
  propagate_tags (andthen well_founded_tactics.unfold_wf_rel well_founded_tactics.unfold_sizeof)

/-- Unfold auxiliary definitions associated with the current declaration. -/
unsafe def unfold_aux : tactic Unit := do
  let tgt ← target
  let name ← decl_name
  let to_unfold := tgt.list_names_with_prefix Name
  guardₓ ¬to_unfold
  -- should we be using simp_lemmas.mk_default?
        simp_lemmas.mk
        to_unfold tgt >>=
      tactic.change

/-- For debugging only. This tactic checks the current state for any
missing dropped goals and restores them. Useful when there are no
goals to solve but "result contains meta-variables". -/
unsafe def recover : tactic Unit :=
  metavariables >>= tactic.set_goals

/-- Like `try { tac }`, but in the case of failure it continues
from the failure state instead of reverting to the original state. -/
unsafe def continue (tac : itactic) : tactic Unit := fun s =>
  result.cases_on (tac s) (fun a => result.success ()) fun e ref => result.success ()

/-- `id { tac }` is the same as `tac`, but it is useful for creating a block scope without
requiring the goal to be solved at the end like `{ tac }`. It can also be used to enclose a
non-interactive tactic for patterns like `tac1; id {tac2}` where `tac2` is non-interactive. -/
@[inline]
protected unsafe def id (tac : itactic) : tactic Unit :=
  tac

/-- `work_on_goal n { tac }` creates a block scope for the `n`-goal,
and does not require that the goal be solved at the end
(any remaining subgoals are inserted back into the list of goals).

Typically usage might look like:
````
intros,
simp,
apply lemma_1,
work_on_goal 3
{ dsimp,
  simp },
refl
````

See also `id { tac }`, which is equivalent to `work_on_goal 1 { tac }`.
-/
unsafe def work_on_goal : parse small_nat → itactic → tactic Unit
  | 0, t => fail "work_on_goal failed: goals are 1-indexed"
  | n + 1, t => do
    let goals ← get_goals
    let earlier_goals := goals.take n
    let later_goals := goals.drop (n + 1)
    set_goals (goals n).toList
    t
    let new_goals ← get_goals
    set_goals (earlier_goals ++ new_goals ++ later_goals)

/-- `swap n` will move the `n`th goal to the front.
`swap` defaults to `swap 2`, and so interchanges the first and second goals.

See also `tactic.interactive.rotate`, which moves the first `n` goals to the back.
-/
unsafe def swap (n := 2) : tactic Unit := do
  let gs ← get_goals
  match gs (n - 1) with
    | some g => set_goals (g :: gs (n - 1))
    | _ => skip

add_tactic_doc
  { Name := "swap", category := DocCategory.tactic, declNames := [`tactic.interactive.swap],
    tags := ["goal management"] }

/-- `rotate` moves the first goal to the back. `rotate n` will do this `n` times.

See also `tactic.interactive.swap`, which moves the `n`th goal to the front.
-/
unsafe def rotate (n := 1) : tactic Unit :=
  tactic.rotate n

add_tactic_doc
  { Name := "rotate", category := DocCategory.tactic, declNames := [`tactic.interactive.rotate],
    tags := ["goal management"] }

/-- Clear all hypotheses starting with `_`, like `_match` and `_let_match`. -/
unsafe def clear_ : tactic Unit :=
  tactic.repeat <| do
    let l ← local_context
    l fun h => do
        let Name.mk_string s p ← return <| local_pp_name h
        guardₓ (s = '_')
        let cl ← infer_type h >>= is_class
        guardₓ ¬cl
        tactic.clear h

add_tactic_doc
  { Name := "clear_", category := DocCategory.tactic, declNames := [`tactic.interactive.clear_],
    tags := ["context management"] }

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- Acts like `have`, but removes a hypothesis with the same name as
this one. For example if the state is `h : p ⊢ goal` and `f : p → q`,
then after `replace h := f h` the goal will be `h : q ⊢ goal`,
where `have h := f h` would result in the state `h : p, h : q ⊢ goal`.
This can be used to simulate the `specialize` and `apply at` tactics
of Coq. -/
unsafe def replace (h : parse («expr ?» ident)) (q₁ : parse («expr ?» (tk ":" *> texpr)))
    (q₂ : parse <| «expr ?» (tk ":=" *> texpr)) : tactic Unit := do
  let h := h.getOrElse `this
  let old ← try_core (get_local h)
  have h q₁ q₂
  match old, q₂ with
    | none, _ => skip
    | some o, some _ => tactic.clear o
    | some o, none => (swap >> tactic.clear o) >> swap

add_tactic_doc
  { Name := "replace", category := DocCategory.tactic, declNames := [`tactic.interactive.replace],
    tags := ["context management"] }

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- Make every proposition in the context decidable.

`classical!` does this more aggressively, such that even if a decidable instance is already
available for a specific proposition, the noncomputable one will be used instead. -/
unsafe def classical (bang : parse <| «expr ?» (tk "!")) :=
  tactic.classical bang.isSome

add_tactic_doc
  { Name := "classical", category := DocCategory.tactic, declNames := [`tactic.interactive.classical],
    tags := ["classical logic", "type class"] }

private unsafe def generalize_arg_p_aux : pexpr → parser (pexpr × Name)
  | app (app (macro _ [const `eq _]) h) (local_const x _ _ _) => pure (h, x)
  | _ => fail "parse error"

private unsafe def generalize_arg_p : parser (pexpr × Name) :=
  with_desc "expr = id" <| parser.pexpr 0 >>= generalize_arg_p_aux

@[nolint def_lemma]
noncomputable theorem generalizeAAux.{u} {α : Sort u} (h : ∀ x : Sort u, (α → x) → x) : α :=
  h α id

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- Like `generalize` but also considers assumptions
specified by the user. The user can also specify to
omit the goal.
-/
unsafe def generalize_hyp (h : parse («expr ?» ident)) (_ : parse <| tk ":") (p : parse generalize_arg_p)
    (l : parse location) : tactic Unit := do
  let h' ← get_unused_name `h
  let x' ← get_unused_name `x
  let g ←
    if ¬l.include_goal then do
        refine (pquote.1 (generalizeAAux _))
        some <$> (Prod.mk <$> tactic.intro x' <*> tactic.intro h')
      else pure none
  let n ← l.get_locals >>= tactic.revert_lst
  generalize h () p
  intron n
  match g with
    | some (x', h') => do
      tactic.apply h'
      tactic.clear h'
      tactic.clear x'
    | none => return ()

add_tactic_doc
  { Name := "generalize_hyp", category := DocCategory.tactic, declNames := [`tactic.interactive.generalize_hyp],
    tags := ["context management"] }

unsafe def compact_decl_aux : List Name → BinderInfo → expr → List expr → tactic (List (List Name × BinderInfo × expr))
  | ns, bi, t, [] => pure [(ns.reverse, bi, t)]
  | ns, bi, t, v'@(local_const n pp bi' t') :: xs => do
    let t' ← infer_type v'
    if bi = bi' ∧ t = t' then compact_decl_aux (pp :: ns) bi t xs
      else do
        let vs ← compact_decl_aux [pp] bi' t' xs
        pure <| (ns, bi, t) :: vs
  | ns, bi, t, _ :: xs => compact_decl_aux ns bi t xs

/-- go from (x₀ : t₀) (x₁ : t₀) (x₂ : t₀) to (x₀ x₁ x₂ : t₀) -/
unsafe def compact_decl : List expr → tactic (List (List Name × BinderInfo × expr))
  | [] => pure []
  | v@(local_const n pp bi t) :: xs => do
    let t ← infer_type v
    compact_decl_aux [pp] bi t xs
  | _ :: xs => compact_decl xs

/-- Remove identity functions from a term. These are normally
automatically generated with terms like `show t, from p` or
`(p : t)` which translate to some variant on `@id t p` in
order to retain the type.
-/
unsafe def clean (q : parse texpr) : tactic Unit := do
  let tgt : expr ← target
  let e ← i_to_expr_strict (pquote.1 (%%ₓq : %%ₓtgt))
  tactic.exact <| e

unsafe def source_fields (missing : List Name) (e : pexpr) : tactic (List (Name × pexpr)) := do
  let e ← to_expr e
  let t ← infer_type e
  let struct_n : Name := t.get_app_fn.const_name
  let fields ← expanded_field_list struct_n
  let exp_fields := fields.filter fun x => x.2 ∈ missing
  exp_fields fun ⟨p, n⟩ => (Prod.mk n ∘ to_pexpr) <$> mk_mapp (n p) [none, some e]

unsafe def collect_struct' : pexpr → StateTₓ (List <| expr × structure_instance_info) tactic pexpr
  | e => do
    let some str ← pure e.get_structure_instance_info | e.traverse collect_struct'
    let v ← monadLift mk_mvar
    modifyₓ (List.cons (v, str))
    pure <| to_pexpr v

unsafe def collect_struct (e : pexpr) : tactic <| pexpr × List (expr × structure_instance_info) :=
  Prod.map id List.reverse <$> (collect_struct' e).run []

unsafe def refine_one (str : structure_instance_info) : tactic <| List (expr × structure_instance_info) := do
  let tgt ← target >>= whnf
  let struct_n : Name := tgt.get_app_fn.const_name
  let exp_fields ← expanded_field_list struct_n
  let missing_f := exp_fields.filter fun f => (f.2 : Name) ∉ str.field_names
  let (src_field_names, src_field_vals) ←
    (@List.unzip Name _ ∘ List.join) <$> str.sources.mmap (source_fields <| missing_f.map Prod.snd)
  let provided := exp_fields.filter fun f => (f.2 : Name) ∈ str.field_names
  let missing_f' := missing_f.filter fun x => x.2 ∉ src_field_names
  let vs ← mk_mvar_list missing_f'.length
  let (field_values, new_goals) ← List.unzip <$> (str.field_values.mmap collect_struct : tactic _)
  let e' ←
    to_expr <|
        pexpr.mk_structure_instance
          { struct := some struct_n, field_names := str.field_names ++ missing_f'.map Prod.snd ++ src_field_names,
            field_values := field_values ++ vs.map to_pexpr ++ src_field_vals }
  tactic.exact e'
  let gs ←
    with_enable_tags
        (mzipWith
          (fun (n : Name × Name) v => do
            set_goals [v]
            try (dsimp_target simp_lemmas.mk)
            apply_auto_param <|> apply_opt_param <|> set_main_tag [`_field, n.2, n.1]
            get_goals)
          missing_f' vs)
  set_goals gs
  return new_goals

unsafe def refine_recursively : expr × structure_instance_info → tactic (List expr)
  | (e, str) => do
    set_goals [e]
    let rs ← refine_one str
    let gs ← get_goals
    let gs' ← rs.mmap refine_recursively
    return <| gs' ++ gs

/-- `refine_struct { .. }` acts like `refine` but works only with structure instance
literals. It creates a goal for each missing field and tags it with the name of the
field so that `have_field` can be used to generically refer to the field currently
being refined.

As an example, we can use `refine_struct` to automate the construction of semigroup
instances:

```lean
refine_struct ( { .. } : semigroup α ),
-- case semigroup, mul
-- α : Type u,
-- ⊢ α → α → α

-- case semigroup, mul_assoc
-- α : Type u,
-- ⊢ ∀ (a b c : α), a * b * c = a * (b * c)
```

`have_field`, used after `refine_struct _`, poses `field` as a local constant
with the type of the field of the current goal:

```lean
refine_struct ({ .. } : semigroup α),
{ have_field, ... },
{ have_field, ... },
```
behaves like
```lean
refine_struct ({ .. } : semigroup α),
{ have field := @semigroup.mul, ... },
{ have field := @semigroup.mul_assoc, ... },
```
-/
unsafe def refine_struct : parse texpr → tactic Unit
  | e => do
    let (x, xs) ← collect_struct e
    refine x
    let gs ← get_goals
    let xs' ← xs.mmap refine_recursively
    set_goals (xs' ++ gs)

/-- `guard_hyp' h : t` fails if the hypothesis `h` does not have type `t`.
We use this tactic for writing tests.
Fixes `guard_hyp` by instantiating meta variables
-/
unsafe def guard_hyp' (n : parse ident) (p : parse <| tk ":" *> texpr) : tactic Unit := do
  let h ← get_local n >>= infer_type >>= instantiate_mvars
  guard_expr_eq h p

/-- `match_hyp h : t` fails if the hypothesis `h` does not match the type `t` (which may be a pattern).
We use this tactic for writing tests.
-/
unsafe def match_hyp (n : parse ident) (p : parse <| tk ":" *> texpr) (m := reducible) : tactic (List expr) := do
  let h ← get_local n >>= infer_type >>= instantiate_mvars
  match_expr p h m

/-- `guard_expr_strict t := e` fails if the expr `t` is not equal to `e`. By contrast
to `guard_expr`, this tests strict (syntactic) equality.
We use this tactic for writing tests.
-/
unsafe def guard_expr_strict (t : expr) (p : parse <| tk ":=" *> texpr) : tactic Unit := do
  let e ← to_expr p
  guardₓ (t = e)

/-- `guard_target_strict t` fails if the target of the main goal is not syntactically `t`.
We use this tactic for writing tests.
-/
unsafe def guard_target_strict (p : parse texpr) : tactic Unit := do
  let t ← target
  guard_expr_strict t p

/-- `guard_hyp_strict h : t` fails if the hypothesis `h` does not have type syntactically equal
to `t`.
We use this tactic for writing tests.
-/
unsafe def guard_hyp_strict (n : parse ident) (p : parse <| tk ":" *> texpr) : tactic Unit := do
  let h ← get_local n >>= infer_type >>= instantiate_mvars
  guard_expr_strict h p

/-- Tests that there are `n` hypotheses in the current context. -/
unsafe def guard_hyp_nums (n : ℕ) : tactic Unit := do
  let k ← local_context
  guardₓ (n = k) <|> fail f! "{k} hypotheses found"

/-- `guard_hyp_mod_implicit h : t` fails if the type of the hypothesis `h`
is not definitionally equal to `t` modulo none transparency
(i.e., unifying the implicit arguments modulo semireducible transparency).
We use this tactic for writing tests.
-/
unsafe def guard_hyp_mod_implicit (n : parse ident) (p : parse <| tk ":" *> texpr) : tactic Unit := do
  let h ← get_local n >>= infer_type >>= instantiate_mvars
  let e ← to_expr p
  is_def_eq h e transparency.none

/-- `guard_target_mod_implicit t` fails if the target of the main goal
is not definitionally equal to `t` modulo none transparency
(i.e., unifying the implicit arguments modulo semireducible transparency).
We use this tactic for writing tests.
-/
unsafe def guard_target_mod_implicit (p : parse texpr) : tactic Unit := do
  let tgt ← target
  let e ← to_expr p
  is_def_eq tgt e transparency.none

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr *»
/-- Test that `t` is the tag of the main goal. -/
unsafe def guard_tags (tags : parse («expr *» ident)) : tactic Unit := do
  let (t : List Name) ← get_main_tag
  guardₓ (t = tags)

/-- `guard_proof_term { t } e` applies tactic `t` and tests whether the resulting proof term
  unifies with `p`. -/
unsafe def guard_proof_term (t : itactic) (p : parse texpr) : itactic := do
  let g :: _ ← get_goals
  let e ← to_expr p
  t
  let g ← instantiate_mvars g
  unify e g

/-- `success_if_fail_with_msg { tac } msg` succeeds if the interactive tactic `tac` fails with
error message `msg` (for test writing purposes). -/
unsafe def success_if_fail_with_msg (tac : tactic.interactive.itactic) :=
  tactic.success_if_fail_with_msg tac

/-- Get the field of the current goal. -/
unsafe def get_current_field : tactic Name := do
  let [_, field, str] ← get_main_tag
  expr.const_name <$> resolve_name (field str)

unsafe def field (n : parse ident) (tac : itactic) : tactic Unit := do
  let gs ← get_goals
  let ts ← gs.mmap get_tag
  let ([g], gs') ← pure <| (List.zipₓ gs ts).partition fun x => x.snd.nth 1 = some n
  set_goals [g.1]
  tac
  done
  set_goals <| gs' Prod.fst

/-- `have_field`, used after `refine_struct _` poses `field` as a local constant
with the type of the field of the current goal:

```lean
refine_struct ({ .. } : semigroup α),
{ have_field, ... },
{ have_field, ... },
```
behaves like
```lean
refine_struct ({ .. } : semigroup α),
{ have field := @semigroup.mul, ... },
{ have field := @semigroup.mul_assoc, ... },
```
-/
unsafe def have_field : tactic Unit :=
  propagate_tags <| (get_current_field >>= mk_const >>= note `field none) >> return ()

/-- `apply_field` functions as `have_field, apply field, clear field` -/
unsafe def apply_field : tactic Unit :=
  propagate_tags <| get_current_field >>= applyc

add_tactic_doc
  { Name := "refine_struct", category := DocCategory.tactic,
    declNames := [`tactic.interactive.refine_struct, `tactic.interactive.apply_field, `tactic.interactive.have_field],
    tags := ["structures"], inheritDescriptionFrom := `tactic.interactive.refine_struct }

/-- `apply_rules hs with attrs n` applies the list of lemmas `hs` and all lemmas tagged with an
attribute from the list `attrs`, as well as the `assumption` tactic on the
first goal and the resulting subgoals, iteratively, at most `n` times.
`n` is optional, equal to 50 by default.
You can pass an `apply_cfg` option argument as `apply_rules hs n opt`.
(A typical usage would be with `apply_rules hs n { md := reducible })`,
which asks `apply_rules` to not unfold `semireducible` definitions (i.e. most)
when checking if a lemma matches the goal.)

For instance:

```lean
@[user_attribute]
meta def mono_rules : user_attribute :=
{ name := `mono_rules,
  descr := "lemmas usable to prove monotonicity" }

attribute [mono_rules] add_le_add mul_le_mul_of_nonneg_right

lemma my_test {a b c d e : real} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
-- any of the following lines solve the goal:
add_le_add (add_le_add (add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_right h2 h3)) h1 ) h2) h3
by apply_rules [add_le_add, mul_le_mul_of_nonneg_right]
by apply_rules with mono_rules
by apply_rules [add_le_add] with mono_rules
```
-/
unsafe def apply_rules (args : parse opt_pexpr_list) (attrs : parse with_ident_list) (n : Nat := 50)
    (opt : ApplyCfg := {  }) : tactic Unit :=
  tactic.apply_rules args attrs n opt

add_tactic_doc
  { Name := "apply_rules", category := DocCategory.tactic, declNames := [`tactic.interactive.apply_rules],
    tags := ["lemma application"] }

unsafe def return_cast (f : Option expr) (t : Option (expr × expr)) (es : List (expr × expr × expr))
    (e x x' eq_h : expr) : tactic (Option (expr × expr) × List (expr × expr × expr)) :=
  (do
      guardₓ ¬e
      unify x x'
      let u ← mk_meta_univ
      let f ← f <|> mk_mapp `` _root_.id [(expr.sort u : expr)]
      let t' ← infer_type e
      let some (f', t) ← pure t | return (some (f, t'), (e, x', eq_h) :: es)
      infer_type e >>= is_def_eq t
      unify f f'
      return (some (f, t), (e, x', eq_h) :: es)) <|>
    return (t, es)

unsafe def list_cast_of_aux (x : expr) (t : Option (expr × expr)) (es : List (expr × expr × expr)) :
    expr → tactic (Option (expr × expr) × List (expr × expr × expr))
  | e@(quote.1 (cast (%%ₓeq_h) (%%ₓx'))) => return_cast none t es e x x' eq_h
  | e@(quote.1 (Eq.mp (%%ₓeq_h) (%%ₓx'))) => return_cast none t es e x x' eq_h
  | e@(quote.1 (Eq.mpr (%%ₓeq_h) (%%ₓx'))) => mk_eq_symm eq_h >>= return_cast none t es e x x'
  | e@(quote.1 (@Eq.subst (%%ₓα) (%%ₓp) (%%ₓa) (%%ₓb) (%%ₓeq_h) (%%ₓx'))) => return_cast p t es e x x' eq_h
  | e@(quote.1 (@Eq.substr (%%ₓα) (%%ₓp) (%%ₓa) (%%ₓb) (%%ₓeq_h) (%%ₓx'))) =>
    mk_eq_symm eq_h >>= return_cast p t es e x x'
  | e@(quote.1 (@Eq.ndrec (%%ₓα) (%%ₓa) (%%ₓf) (%%ₓx') _ (%%ₓeq_h))) => return_cast f t es e x x' eq_h
  | e@(quote.1 (@Eq.recOnₓ (%%ₓα) (%%ₓa) (%%ₓf) (%%ₓb) (%%ₓeq_h) (%%ₓx'))) => return_cast f t es e x x' eq_h
  | e => return (t, es)

unsafe def list_cast_of (x tgt : expr) : tactic (List (expr × expr × expr)) :=
  (List.reverse ∘ Prod.snd) <$> tgt.mfold (none, []) fun e i es => list_cast_of_aux x es.1 es.2 e

private unsafe def h_generalize_arg_p_aux : pexpr → parser (pexpr × Name)
  | app (app (macro _ [const `heq _]) h) (local_const x _ _ _) => pure (h, x)
  | _ => fail "parse error"

private unsafe def h_generalize_arg_p : parser (pexpr × Name) :=
  with_desc "expr == id" <| parser.pexpr 0 >>= h_generalize_arg_p_aux

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- `h_generalize Hx : e == x` matches on `cast _ e` in the goal and replaces it with
`x`. It also adds `Hx : e == x` as an assumption. If `cast _ e` appears multiple
times (not necessarily with the same proof), they are all replaced by `x`. `cast`
`eq.mp`, `eq.mpr`, `eq.subst`, `eq.substr`, `eq.rec` and `eq.rec_on` are all treated
as casts.

- `h_generalize Hx : e == x with h` adds hypothesis `α = β` with `e : α, x : β`;
- `h_generalize Hx : e == x with _` chooses automatically chooses the name of
  assumption `α = β`;
- `h_generalize! Hx : e == x` reverts `Hx`;
- when `Hx` is omitted, assumption `Hx : e == x` is not added.
-/
unsafe def h_generalize (rev : parse («expr ?» (tk "!"))) (h : parse («expr ?» ident_)) (_ : parse (tk ":"))
    (arg : parse h_generalize_arg_p) (eqs_h : parse (tk "with" *> pure <$> ident_ <|> pure [])) : tactic Unit := do
  let (e, n) := arg
  let h' := if h = `_ then none else h
  let h' ← (h' : tactic Name) <|> get_unused_name ("h" ++ n.toString : Stringₓ)
  let e ← to_expr e
  let tgt ← target
  let (e, x, eq_h) :: es ← list_cast_of e tgt | fail "no cast found"
  interactive.generalize h' () (to_pexpr e, n)
  let asm ← get_local h'
  let v ← get_local n
  let hs ← es.mmap fun ⟨e, _⟩ => mk_app `eq [e, v]
  (eqs_h [e]).mmap' fun ⟨h, e⟩ => do
      let h ← if h ≠ `_ then pure h else get_unused_name `h
      () <$ note h none eq_h
  hs fun h => do
      let h' ← assert `h h
      tactic.exact asm
      try (rewrite_target h')
      tactic.clear h'
  when h do
      ((to_expr (pquote.1 (heq_of_eq_rec_leftₓ (%%ₓeq_h) (%%ₓasm))) <|>
              to_expr (pquote.1 (heq_of_cast_eq (%%ₓeq_h) (%%ₓasm)))) >>=
            note h' none) >>
          pure ()
  tactic.clear asm
  when rev (interactive.revert [n])

add_tactic_doc
  { Name := "h_generalize", category := DocCategory.tactic, declNames := [`tactic.interactive.h_generalize],
    tags := ["context management"] }

/-- Tests whether `t` is definitionally equal to `p`. The difference with `guard_expr_eq` is that
  this uses definitional equality instead of alpha-equivalence. -/
unsafe def guard_expr_eq' (t : expr) (p : parse <| tk ":=" *> texpr) : tactic Unit := do
  let e ← to_expr p
  is_def_eq t e

/-- `guard_target' t` fails if the target of the main goal is not definitionally equal to `t`.
We use this tactic for writing tests.
The difference with `guard_target` is that this uses definitional equality instead of
alpha-equivalence.
-/
unsafe def guard_target' (p : parse texpr) : tactic Unit := do
  let t ← target
  guard_expr_eq' t p

add_tactic_doc
  { Name := "guard_target'", category := DocCategory.tactic, declNames := [`tactic.interactive.guard_target'],
    tags := ["testing"] }

/-- Tries to solve the goal using a canonical proof of `true` or the `reflexivity` tactic.
Unlike `trivial` or `trivial'`, does not the `contradiction` tactic.
-/
unsafe def triv : tactic Unit :=
  tactic.triv <|> tactic.reflexivity <|> fail "triv tactic failed"

add_tactic_doc
  { Name := "triv", category := DocCategory.tactic, declNames := [`tactic.interactive.triv], tags := ["finishing"] }

/-- A weaker version of `trivial` that tries to solve the goal using a canonical proof of `true` or the
`reflexivity` tactic (unfolding only `reducible` constants, so can fail faster than `trivial`),
and otherwise tries the `contradiction` tactic. -/
unsafe def trivial' : tactic Unit :=
  tactic.triv' <|> tactic.reflexivity reducible <|> tactic.contradiction <|> fail "trivial' tactic failed"

add_tactic_doc
  { Name := "trivial'", category := DocCategory.tactic, declNames := [`tactic.interactive.trivial'],
    tags := ["finishing"] }

/-- Similar to `existsi`. `use x` will instantiate the first term of an `∃` or `Σ` goal with `x`. It
will then try to close the new goal using `trivial'`, or try to simplify it by applying
`exists_prop`. Unlike `existsi`, `x` is elaborated with respect to the expected type.
`use` will alternatively take a list of terms `[x0, ..., xn]`.

`use` will work with constructors of arbitrary inductive types.

Examples:
```lean
example (α : Type) : ∃ S : set α, S = S :=
by use ∅

example : ∃ x : ℤ, x = x :=
by use 42

example : ∃ n > 0, n = n :=
begin
  use 1,
  -- goal is now 1 > 0 ∧ 1 = 1, whereas it would be ∃ (H : 1 > 0), 1 = 1 after existsi 1.
  exact ⟨zero_lt_one, rfl⟩,
end

example : ∃ a b c : ℤ, a + b + c = 6 :=
by use [1, 2, 3]

example : ∃ p : ℤ × ℤ, p.1 = 1 :=
by use ⟨1, 42⟩

example : Σ x y : ℤ, (ℤ × ℤ) × ℤ :=
by use [1, 2, 3, 4, 5]

inductive foo
| mk : ℕ → bool × ℕ → ℕ → foo

example : foo :=
by use [100, tt, 4, 3]
```
-/
unsafe def use (l : parse pexpr_list_or_texpr) : tactic Unit :=
  focus1 <|
    andthen (tactic.use l)
      (try
        (trivial' <|> do
          let quote.1 (Exists (%%ₓp)) ← target
          (to_expr (pquote.1 exists_prop.mpr) >>= tactic.apply) >> skip))

add_tactic_doc
  { Name := "use", category := DocCategory.tactic, declNames := [`tactic.interactive.use, `tactic.interactive.existsi],
    tags := ["logic"], inheritDescriptionFrom := `tactic.interactive.use }

/-- `clear_aux_decl` clears every `aux_decl` in the local context for the current goal.
This includes the induction hypothesis when using the equation compiler and
`_let_match` and `_fun_match`.

It is useful when using a tactic such as `finish`, `simp *` or `subst` that may use these
auxiliary declarations, and produce an error saying the recursion is not well founded.

```lean
example (n m : ℕ) (h₁ : n = m) (h₂ : ∃ a : ℕ, a = n ∧ a = m) : 2 * m = 2 * n :=
let ⟨a, ha⟩ := h₂ in
begin
  clear_aux_decl, -- subst will fail without this line
  subst h₁
end

example (x y : ℕ) (h₁ : ∃ n : ℕ, n * 1 = 2) (h₂ : 1 + 1 = 2 → x * 1 = y) : x = y :=
let ⟨n, hn⟩ := h₁ in
begin
  clear_aux_decl, -- finish produces an error without this line
  finish
end
```
-/
unsafe def clear_aux_decl : tactic Unit :=
  tactic.clear_aux_decl

add_tactic_doc
  { Name := "clear_aux_decl", category := DocCategory.tactic,
    declNames := [`tactic.interactive.clear_aux_decl, `tactic.clear_aux_decl], tags := ["context management"],
    inheritDescriptionFrom := `tactic.interactive.clear_aux_decl }

unsafe def loc.get_local_pp_names : Loc → tactic (List Name)
  | loc.wildcard => List.map expr.local_pp_name <$> local_context
  | loc.ns l => return l.reduceOption

unsafe def loc.get_local_uniq_names (l : Loc) : tactic (List Name) :=
  List.map expr.local_uniq_name <$> l.get_locals

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- The logic of `change x with y at l` fails when there are dependencies.
`change'` mimics the behavior of `change`, except in the case of `change x with y at l`.
In this case, it will correctly replace occurences of `x` with `y` at all possible hypotheses
in `l`. As long as `x` and `y` are defeq, it should never fail.
-/
unsafe def change' (q : parse texpr) : parse («expr ?» (tk "with" *> texpr)) → parse location → tactic Unit
  | none, loc.ns [none] => do
    let e ← i_to_expr q
    change_core e none
  | none, loc.ns [some h] => do
    let eq ← i_to_expr q
    let eh ← get_local h
    change_core Eq (some eh)
  | none, _ => fail "change-at does not support multiple locations"
  | some w, l => do
    let l' ← loc.get_local_pp_names l
    l' fun e => try (change_with_at q w e)
    when l <| change q w (loc.ns [none])

add_tactic_doc
  { Name := "change'", category := DocCategory.tactic,
    declNames := [`tactic.interactive.change', `tactic.interactive.change], tags := ["renaming"],
    inheritDescriptionFrom := `tactic.interactive.change' }

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
private unsafe def opt_dir_with : parser (Option (Bool × Name)) :=
  «expr ?» (tk "with" *> ((fun arrow h => (Option.isSome arrow, h)) <$> «expr ?» (tk "<-") <*> ident))

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- `set a := t with h` is a variant of `let a := t`. It adds the hypothesis `h : a = t` to
the local context and replaces `t` with `a` everywhere it can.

`set a := t with ←h` will add `h : t = a` instead.

`set! a := t with h` does not do any replacing.

```lean
example (x : ℕ) (h : x = 3)  : x + x + x = 9 :=
begin
  set y := x with ←h_xy,
/-
x : ℕ,
y : ℕ := x,
h_xy : x = y,
h : y = 3
⊢ y + y + y = 9
-/
end
```
-/
unsafe def set (h_simp : parse («expr ?» (tk "!"))) (a : parse ident) (tp : parse («expr ?» (tk ":" *> texpr)))
    (_ : parse (tk ":=")) (pv : parse texpr) (rev_name : parse opt_dir_with) := do
  let tp ←
    i_to_expr <|
        let t := tp.getOrElse pexpr.mk_placeholder
        pquote.1 (%%ₓt : Sort _)
  let pv ← to_expr (pquote.1 (%%ₓpv : %%ₓtp))
  let tp ← instantiate_mvars tp
  definev a tp pv
  when h_simp <| change' (pquote.1 (%%ₓpv)) (some (expr.const a [])) <| Interactive.Loc.wildcard
  match rev_name with
    | some (flip, id) => do
      let nv ← get_local a
      mk_app `eq (cond flip [pv, nv] [nv, pv]) >>= assert id
      reflexivity
    | none => skip

add_tactic_doc
  { Name := "set", category := DocCategory.tactic, declNames := [`tactic.interactive.set],
    tags := ["context management"] }

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr *»
/-- `clear_except h₀ h₁` deletes all the assumptions it can except for `h₀` and `h₁`.
-/
unsafe def clear_except (xs : parse («expr *» ident)) : tactic Unit := do
  let n ← xs.mmap (try_core ∘ get_local) >>= revert_lst ∘ List.filterMap id
  let ls ← local_context
  ls <| try ∘ tactic.clear
  intron_no_renames n

add_tactic_doc
  { Name := "clear_except", category := DocCategory.tactic, declNames := [`tactic.interactive.clear_except],
    tags := ["context management"] }

unsafe def format_names (ns : List Name) : format :=
  format.join <| List.intersperse " " (ns.map to_fmt)

private unsafe def indent_bindents (l r : Stringₓ) : Option (List Name) → expr → tactic format
  | none, e => do
    let e ← pp e
    f!"{(← l)}{(← format.nest l e)}{← r}"
  | some ns, e => do
    let e ← pp e
    let ns := format_names ns
    let margin := l.length + ns.toString.length + " : ".length
    f!"{(← l)}{(← ns)} : {(← format.nest margin e)}{← r}"

private unsafe def format_binders : List Name × BinderInfo × expr → tactic format
  | (ns, BinderInfo.default, t) => indent_bindents "(" ")" ns t
  | (ns, BinderInfo.implicit, t) => indent_bindents "{" "}" ns t
  | (ns, BinderInfo.strict_implicit, t) => indent_bindents "⦃" "⦄" ns t
  | ([n], BinderInfo.inst_implicit, t) =>
    if "_".isPrefixOf n.toString then indent_bindents "[" "]" none t else indent_bindents "[" "]" [n] t
  | (ns, BinderInfo.inst_implicit, t) => indent_bindents "[" "]" ns t
  | (ns, BinderInfo.aux_decl, t) => indent_bindents "(" ")" ns t

private unsafe def partition_vars' (s : name_set) : List expr → List expr → List expr → tactic (List expr × List expr)
  | [], as, bs => pure (as.reverse, bs.reverse)
  | x :: xs, as, bs => do
    let t ← infer_type x
    if t s then partition_vars' xs as (x :: bs) else partition_vars' xs (x :: as) bs

private unsafe def partition_vars : tactic (List expr × List expr) := do
  let ls ← local_context
  partition_vars' (name_set.of_list <| ls expr.local_uniq_name) ls [] []

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr *»
/-- Format the current goal as a stand-alone example. Useful for testing tactics
or creating [minimal working examples](https://leanprover-community.github.io/mwe.html).

* `extract_goal`: formats the statement as an `example` declaration
* `extract_goal my_decl`: formats the statement as a `lemma` or `def` declaration
  called `my_decl`
* `extract_goal with i j k:` only use local constants `i`, `j`, `k` in the declaration

Examples:

```lean
example (i j k : ℕ) (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k :=
begin
  extract_goal,
     -- prints:
     -- example (i j k : ℕ) (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k :=
     -- begin
     --   admit,
     -- end
  extract_goal my_lemma
     -- prints:
     -- lemma my_lemma (i j k : ℕ) (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k :=
     -- begin
     --   admit,
     -- end
end

example {i j k x y z w p q r m n : ℕ} (h₀ : i ≤ j) (h₁ : j ≤ k) (h₁ : k ≤ p) (h₁ : p ≤ q) : i ≤ k :=
begin
  extract_goal my_lemma,
    -- prints:
    -- lemma my_lemma {i j k x y z w p q r m n : ℕ}
    --   (h₀ : i ≤ j)
    --   (h₁ : j ≤ k)
    --   (h₁ : k ≤ p)
    --   (h₁ : p ≤ q) :
    --   i ≤ k :=
    -- begin
    --   admit,
    -- end

  extract_goal my_lemma with i j k
    -- prints:
    -- lemma my_lemma {p i j k : ℕ}
    --   (h₀ : i ≤ j)
    --   (h₁ : j ≤ k)
    --   (h₁ : k ≤ p) :
    --   i ≤ k :=
    -- begin
    --   admit,
    -- end
end

example : true :=
begin
  let n := 0,
  have m : ℕ, admit,
  have k : fin n, admit,
  have : n + m + k.1 = 0, extract_goal,
    -- prints:
    -- example (m : ℕ)  : let n : ℕ := 0 in ∀ (k : fin n), n + m + k.val = 0 :=
    -- begin
    --   intros n k,
    --   admit,
    -- end
end
```

-/
unsafe def extract_goal (print_use : parse <| tk "!" *> pure true <|> pure false) (n : parse («expr ?» ident))
    (vs : parse («expr ?» (tk "with" *> «expr *» ident))) : tactic Unit := do
  let tgt ← target
  solve_aux tgt <| do
      let ((cxt₀, cxt₁, ls, tgt), _) ←
        solve_aux tgt <| do
            vs clear_except
            let ls ← local_context
            let ls ← ls <| succeeds ∘ is_local_def
            let n ← revert_lst ls
            let (c₀, c₁) ← partition_vars
            let tgt ← target
            let ls ← intron' n
            pure (c₀, c₁, ls, tgt)
      let is_prop ← is_prop tgt
      let title :=
        match n, is_prop with
        | none, _ => to_fmt "example"
        | some n, tt => f! "lemma {n}"
        | some n, ff => f! "def {n}"
      let cxt₀ ← compact_decl cxt₀ >>= List.mmapₓ format_binders
      let cxt₁ ← compact_decl cxt₁ >>= List.mmapₓ format_binders
      let stmt ← f!"{← tgt} :="
      let fmt :=
        format.group <|
          format.nest 2 <|
            title ++ cxt₀ (fun acc x => Acc ++ format.group (format.line ++ x)) "" ++
                    format.join (List.map (fun x => format.line ++ x) cxt₁) ++
                  " :" ++
                format.line ++
              stmt
      trace <| fmt <| options.mk `pp.width 80
      let var_names := format.intercalate " " <| ls (to_fmt ∘ local_pp_name)
      let call_intron :=
        if ls then to_fmt ""
        else
          f! "
              intros {var_names},"
      ← do
          dbg_trace "begin{← call_intron}
              admit,
            end
            "
  skip

add_tactic_doc
  { Name := "extract_goal", category := DocCategory.tactic, declNames := [`tactic.interactive.extract_goal],
    tags := ["goal management", "proof extraction", "debugging"] }

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- `inhabit α` tries to derive a `nonempty α` instance and then upgrades this
to an `inhabited α` instance.
If the target is a `Prop`, this is done constructively;
otherwise, it uses `classical.choice`.

```lean
example (α) [nonempty α] : ∃ a : α, true :=
begin
  inhabit α,
  existsi default,
  trivial
end
```
-/
unsafe def inhabit (t : parse parser.pexpr) (inst_name : parse («expr ?» ident)) : tactic Unit := do
  let ty ← i_to_expr t
  let nm ← returnopt inst_name <|> get_unused_name `inst
  let tgt ← target
  let tgt_is_prop ← is_prop tgt
  if tgt_is_prop then do
      decorate_error "could not infer nonempty instance:" <|
          mk_mapp `` Nonempty.elim_to_inhabited [ty, none, tgt] >>= tactic.apply
      introI nm
    else do
      decorate_error "could not infer nonempty instance:" <|
          mk_mapp `` Classical.inhabitedOfNonempty' [ty, none] >>= note nm none
      resetI

add_tactic_doc
  { Name := "inhabit", category := DocCategory.tactic, declNames := [`tactic.interactive.inhabit],
    tags := ["context management", "type class"] }

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr *»
/-- `revert_deps n₁ n₂ ...` reverts all the hypotheses that depend on one of `n₁, n₂, ...`
It does not revert `n₁, n₂, ...` themselves (unless they depend on another `nᵢ`). -/
unsafe def revert_deps (ns : parse («expr *» ident)) : tactic Unit :=
  propagate_tags <| (ns.mmap get_local >>= revert_reverse_dependencies_of_hyps) >> skip

add_tactic_doc
  { Name := "revert_deps", category := DocCategory.tactic, declNames := [`tactic.interactive.revert_deps],
    tags := ["context management", "goal management"] }

/-- `revert_after n` reverts all the hypotheses after `n`. -/
unsafe def revert_after (n : parse ident) : tactic Unit :=
  propagate_tags <| (get_local n >>= tactic.revert_after) >> skip

add_tactic_doc
  { Name := "revert_after", category := DocCategory.tactic, declNames := [`tactic.interactive.revert_after],
    tags := ["context management", "goal management"] }

/-- Reverts all local constants on which the target depends (recursively). -/
unsafe def revert_target_deps : tactic Unit :=
  propagate_tags <| tactic.revert_target_deps >> skip

add_tactic_doc
  { Name := "revert_target_deps", category := DocCategory.tactic, declNames := [`tactic.interactive.revert_target_deps],
    tags := ["context management", "goal management"] }

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr *»
/-- `clear_value n₁ n₂ ...` clears the bodies of the local definitions `n₁, n₂ ...`, changing them
into regular hypotheses. A hypothesis `n : α := t` is changed to `n : α`. -/
unsafe def clear_value (ns : parse («expr *» ident)) : tactic Unit :=
  propagate_tags <| ns.reverse.mmap get_local >>= tactic.clear_value

add_tactic_doc
  { Name := "clear_value", category := DocCategory.tactic, declNames := [`tactic.interactive.clear_value],
    tags := ["context management"] }

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- `generalize' : e = x` replaces all occurrences of `e` in the target with a new hypothesis `x` of
the same type.

`generalize' h : e = x` in addition registers the hypothesis `h : e = x`.

`generalize'` is similar to `generalize`. The difference is that `generalize' : e = x` also
succeeds when `e` does not occur in the goal. It is similar to `set`, but the resulting hypothesis
`x` is not a local definition.
-/
unsafe def generalize' (h : parse («expr ?» ident)) (_ : parse <| tk ":") (p : parse generalize_arg_p) : tactic Unit :=
  propagate_tags <| do
    let (p, x) := p
    let e ← i_to_expr p
    let some h ← pure h | tactic.generalize' e x >> skip
    let tgt
      ←-- `h` is given, the regular implementation of `generalize` works.
        target
    let tgt' ←
      (do
            let ⟨tgt', _⟩ ← solve_aux tgt (tactic.generalize e x >> target)
            to_expr (pquote.1 (∀ x, (%%ₓe) = x → %%ₓtgt' 0 1))) <|>
          to_expr (pquote.1 (∀ x, (%%ₓe) = x → %%ₓtgt))
    let t ← assert h tgt'
    swap
    exact (pquote.1 ((%%ₓt) (%%ₓe) rfl))
    intro x
    intro h

add_tactic_doc
  { Name := "generalize'", category := DocCategory.tactic, declNames := [`tactic.interactive.generalize'],
    tags := ["context management"] }

/-- If the expression `q` is a local variable with type `x = t` or `t = x`, where `x` is a local
constant, `tactic.interactive.subst' q` substitutes `x` by `t` everywhere in the main goal and
then clears `q`.
If `q` is another local variable, then we find a local constant with type `q = t` or `t = q` and
substitute `t` for `q`.

Like `tactic.interactive.subst`, but fails with a nicer error message if the substituted variable is
a local definition. It is trickier to fix this in core, since `tactic.is_local_def` is in mathlib.
-/
unsafe def subst' (q : parse texpr) : tactic Unit := do
  (i_to_expr q >>= tactic.subst') >> try (tactic.reflexivity reducible)

add_tactic_doc
  { Name := "subst'", category := DocCategory.tactic, declNames := [`tactic.interactive.subst'],
    tags := ["context management"] }

end Interactive

end Tactic

