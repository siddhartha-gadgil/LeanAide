/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Mathbin.Tactic.Core

/-!
# The `generalizes` tactic

This module defines the `tactic.generalizes'` tactic and its interactive version
`tactic.interactive.generalizes`. These work like `generalize`, but they can
generalize over multiple expressions at once. This is particularly handy when
there are dependencies between the expressions, in which case `generalize` will
usually fail but `generalizes` may succeed.

## Implementation notes

To generalize the target `T` over expressions `j₁ : J₁, ..., jₙ : Jₙ`, we first
create the new target type

    T' = ∀ (k₁ : J₁) ... (kₙ : Jₙ) (k₁_eq : k₁ = j₁) ... (kₙ_eq : kₙ == jₙ), U

where `U` is `T` with any occurrences of the `jᵢ` replaced by the corresponding
`kᵢ`. Note that some of the `kᵢ_eq` may be heterogeneous; this happens when
there are dependencies between the `jᵢ`. The construction of `T'` is performed
by `generalizes.step1` and `generalizes.step2`.

Having constructed `T'`, we can `assert` it and use it to construct a proof of
the original target by instantiating the binders with

    j₁ ... jₙ (eq.refl j₁) ... (heq.refl jₙ).

This leaves us with a generalized goal. This construction is performed by
`generalizes.step3`.
-/


universe u v w

namespace Tactic

open Expr

namespace Generalizes

/-- Input:

- Target expression `e`.
- List of expressions `jᵢ` to be generalised, along with a name for the local
  const that will replace them. The `jᵢ` must be in dependency order:
  `[n, fin n]` is okay but `[fin n, n]` is not.

Output:

- List of new local constants `kᵢ`, one for each `jᵢ`.
- `e` with the `jᵢ` replaced by the `kᵢ`, i.e. `e[jᵢ := kᵢ]...[j₀ := k₀]`.

Note that the substitution also affects the types of the `kᵢ`: If `jᵢ : Jᵢ` then
`kᵢ : Jᵢ[jᵢ₋₁ := kᵢ₋₁]...[j₀ := k₀]`.

The transparency `md` and the boolean `unify` are passed to `kabstract` when we
abstract over occurrences of the `jᵢ` in `e`.
-/
unsafe def step1 (md : Transparency) (unify : Bool) (e : expr) (to_generalize : List (Name × expr)) :
    tactic (expr × List expr) := do
  let go : Name × expr → expr × List expr → tactic (expr × List expr) := fun ⟨n, j⟩ ⟨e, ks⟩ => do
    let J ← infer_type j
    let k ← mk_local' n BinderInfo.default J
    let e ← kreplace e j k md unify
    let ks ← ks.mmap fun k' => kreplace k' j k md unify
    pure (e, k :: ks)
  to_generalize go (e, [])

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Input: for each equation that should be generated: the equation name, the
argument `jᵢ` and the corresponding local constant `kᵢ` from step 1.

Output: for each element of the input list a new local constant of type
`jᵢ = kᵢ` or `jᵢ == kᵢ` and a proof of `jᵢ = jᵢ` or `jᵢ == jᵢ`.

The transparency `md` is used when determining whether the type of `jᵢ` is defeq
to the type of `kᵢ` (and thus whether to generate a homogeneous or heterogeneous
equation).
-/
unsafe def step2 (md : Transparency) (to_generalize : List (Name × expr × expr)) : tactic (List (expr × expr)) :=
  to_generalize.mmap fun ⟨n, j, k⟩ => do
    let J ← infer_type j
    let K ← infer_type k
    let sort u ← infer_type K |
      "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
    let homogeneous ← succeeds <| is_def_eq J K md
    let ⟨eq_type, eq_proof⟩ :=
      if homogeneous then ((const `eq [u]) K k j, (const `eq.refl [u]) J j)
      else ((const `heq [u]) K k J j, (const `heq.refl [u]) J j)
    let eq ← mk_local' n BinderInfo.default eq_type
    pure (Eq, eq_proof)

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Input: The `jᵢ`; the local constants `kᵢ` from step 1; the equations and their
proofs from step 2.

This step is the first one that changes the goal (and also the last one
overall). It asserts the generalized goal, then derives the current goal from
it. This leaves us with the generalized goal.
-/
unsafe def step3 (e : expr) (js ks eqs eq_proofs : List expr) : tactic Unit :=
  focus1 <| do
    let new_target_type := (e.pis eqs).pis ks
    type_check new_target_type <|>
        "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
    let n ← mk_fresh_name
    let new_target ← assert n new_target_type
    swap
    let target_proof := new_target.mk_app <| js ++ eq_proofs
    exact target_proof

end Generalizes

open Generalizes

/-- Generalizes the target over each of the expressions in `args`. Given
`args = [(a₁, h₁, arg₁), ...]`, this changes the target to

    ∀ (a₁ : T₁) ... (h₁ : a₁ = arg₁) ..., U

where `U` is the current target with every occurrence of `argᵢ` replaced by
`aᵢ`. A similar effect can be achieved by using `generalize` once for each of
the `args`, but if there are dependencies between the `args`, this may fail to
perform some generalizations.

The replacement is performed using keyed matching/unification with transparency
`md`. `unify` determines whether matching or unification is used. See
`kabstract`.

The `args` must be given in dependency order, so `[n, fin n]` is okay but
`[fin n, n]` will result in an error.

After generalizing the `args`, the target type may no longer type check.
`generalizes'` will then raise an error.
-/
unsafe def generalizes' (args : List (Name × Option Name × expr)) (md := semireducible) (unify := true) : tactic Unit :=
  do
  let tgt ← target
  let stage1_args := args.map fun ⟨n, _, j⟩ => (n, j)
  let ⟨e, ks⟩ ← step1 md unify tgt stage1_args
  let stage2_args : List (Option (Name × expr × expr)) :=
    args.map₂ (fun ⟨_, eq_name, j⟩ k => eq_name.map fun eq_name => (eq_name, j, k)) ks
  let stage2_args := stage2_args.reduceOption
  let eqs_and_proofs ← step2 md stage2_args
  let eqs := eqs_and_proofs.map Prod.fst
  let eq_proofs := eqs_and_proofs.map Prod.snd
  let js := args.map (Prod.snd ∘ Prod.snd)
  step3 e js ks eqs eq_proofs

/-- Like `generalizes'`, but also introduces the generalized constants and their
associated equations into the context.
-/
unsafe def generalizes_intro (args : List (Name × Option Name × expr)) (md := semireducible) (unify := true) :
    tactic (List expr × List expr) := do
  generalizes' args md unify
  let ks ← intron' args.length
  let eqs ← intron' <| args.countp fun x => x.snd.fst.isSome
  pure (ks, eqs)

namespace Interactive

setup_tactic_parser

private unsafe def generalizes_arg_parser_eq : pexpr → lean.parser (pexpr × Name)
  | app (app (macro _ [const `eq _]) e) (local_const x _ _ _) => pure (e, x)
  | app (app (macro _ [const `heq _]) e) (local_const x _ _ _) => pure (e, x)
  | _ => failure

private unsafe def generalizes_arg_parser : lean.parser (Name × Option Name × pexpr) :=
  with_desc "(id :)? expr = id" <| do
    let lhs ← lean.parser.pexpr 0
    (tk ":" >>
          match lhs with
          | local_const hyp_name _ _ _ => do
            let (arg, arg_name) ← lean.parser.pexpr 0 >>= generalizes_arg_parser_eq
            pure (arg_name, some hyp_name, arg)
          | _ => failure) <|>
        do
        let (arg, arg_name) ← generalizes_arg_parser_eq lhs
        pure (arg_name, none, arg)

private unsafe def generalizes_args_parser : lean.parser (List (Name × Option Name × pexpr)) :=
  with_desc "[(id :)? expr = id, ...]" <| tk "[" *> sep_by (tk ",") generalizes_arg_parser <* tk "]"

/-- Generalizes the target over multiple expressions. For example, given the goal

    P : ∀ n, fin n → Prop
    n : ℕ
    f : fin n
    ⊢ P (nat.succ n) (fin.succ f)

you can use `generalizes [n'_eq : nat.succ n = n', f'_eq : fin.succ f == f']` to
get

    P : ∀ n, fin n → Prop
    n : ℕ
    f : fin n
    n' : ℕ
    n'_eq : n' = nat.succ n
    f' : fin n'
    f'_eq : f' == fin.succ f
    ⊢ P n' f'

The expressions must be given in dependency order, so
`[f'_eq : fin.succ f == f', n'_eq : nat.succ n = n']` would fail since the type
of `fin.succ f` is `nat.succ n`.

You can choose to omit some or all of the generated equations. For the above
example, `generalizes [nat.succ n = n', fin.succ f == f']` gets you

    P : ∀ n, fin n → Prop
    n : ℕ
    f : fin n
    n' : ℕ
    f' : fin n'
    ⊢ P n' f'

After generalization, the target type may no longer type check. `generalizes`
will then raise an error.
-/
unsafe def generalizes (args : parse generalizes_args_parser) : tactic Unit :=
  propagate_tags <| do
    let args ←
      args.mmap fun ⟨arg_name, hyp_name, arg⟩ => do
          let arg ← to_expr arg
          pure (arg_name, hyp_name, arg)
    generalizes_intro args
    pure ()

add_tactic_doc
  { Name := "generalizes", category := DocCategory.tactic, declNames := [`tactic.interactive.generalizes],
    tags := ["context management"], inheritDescriptionFrom := `tactic.interactive.generalizes }

end Interactive

end Tactic

