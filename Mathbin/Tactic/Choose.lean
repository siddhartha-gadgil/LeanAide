/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Mario Carneiro
-/
import Mathbin.Logic.Function.Basic
import Mathbin.Tactic.Core

/-!
# `choose` tactic

Performs Skolemization, that is, given `h : ∀ a:α, ∃ b:β, p a b |- G` produces
`f : α → β, hf: ∀ a, p a (f a) |- G`.
-/


namespace Tactic

/-- Given `α : Sort u`, `nonemp : nonempty α`, `p : α → Prop`, a context of local variables
`ctxt`, and a pair of an element `val : α` and `spec : p val`,
`mk_sometimes u α nonemp p ctx (val, spec)` produces another pair `val', spec'`
such that `val'` does not have any free variables from elements of `ctxt` whose types are
propositions. This is done by applying `function.sometimes` to abstract over all the propositional
arguments. -/
unsafe def mk_sometimes (u : level) (α nonemp p : expr) : List expr → expr × expr → tactic (expr × expr)
  | [], (val, spec) => pure (val, spec)
  | e :: ctxt, (val, spec) => do
    let (val, spec) ← mk_sometimes ctxt (val, spec)
    let t ← infer_type e
    let b ← is_prop t
    pure <|
        if b then
          let val' := expr.bind_lambda val e
          (expr.const `` Function.sometimes [level.zero, u] t α nonemp val',
            expr.const `` Function.sometimes_spec [u] t α nonemp p val' e spec)
        else (val, spec)

/-- Changes `(h : ∀xs, ∃a:α, p a) ⊢ g` to `(d : ∀xs, a) (s : ∀xs, p (d xs)) ⊢ g` and
`(h : ∀xs, p xs ∧ q xs) ⊢ g` to `(d : ∀xs, p xs) (s : ∀xs, q xs) ⊢ g`.
`choose1` returns a pair of the second local constant it introduces,
and the error result (see below).

If `nondep` is true and `α` is inhabited, then it will remove the dependency of `d` on
all propositional assumptions in `xs`. For example if `ys` are propositions then
`(h : ∀xs ys, ∃a:α, p a) ⊢ g` becomes `(d : ∀xs, a) (s : ∀xs ys, p (d xs)) ⊢ g`.

The second value returned by `choose1` is the result of nondep elimination:
* `none`: nondep elimination was not attempted or was not applicable
* `some none`: nondep elimination was successful
* ``some (some `(nonempty α))``: nondep elimination was unsuccessful
  because we could not find a `nonempty α` instance
-/
unsafe def choose1 (nondep : Bool) (h : expr) (data : Name) (spec : Name) : tactic (expr × Option (Option expr)) := do
  let t ← infer_type h
  let (ctxt, t) ← whnf t >>= open_pis
  let t ← whnf t Transparency.all
  match t with
    | quote.1 (@Exists (%%ₓα) (%%ₓp)) => do
      let α_t ← infer_type α
      let expr.sort u ← whnf α_t transparency.all
      let (ne_fail, nonemp) ←
        if nondep then do
            let ne := expr.const `` Nonempty [u] α
            let nonemp ←
              try_core
                  (mk_instance Ne <|>
                    retrieve' do
                      let m ← mk_meta_var Ne
                      set_goals [m]
                      ctxt fun e => do
                          let b ← is_proof e
                          Monadₓ.unlessb b <| (mk_app `` Nonempty.intro [e] >>= note_anon none) $> ()
                      reset_instance_cache
                      apply_instance
                      instantiate_mvars m)
            pure (some (Option.guard (fun _ => nonemp) Ne), nonemp)
          else pure (none, none)
      let ctxt' ← if nonemp then ctxt fun e => bnot <$> is_proof e else pure ctxt
      let value ← mk_local_def data (α ctxt')
      let t' ← head_beta (p (value ctxt'))
      let spec ← mk_local_def spec (t' ctxt)
      let (value_proof, spec_proof) ←
        nonemp pure (fun nonemp => mk_sometimes u α nonemp p ctxt)
            (expr.const `` Classical.some [u] α p (h ctxt), expr.const `` Classical.some_spec [u] α p (h ctxt))
      dependent_pose_core [(value, value_proof ctxt'), (spec, spec_proof ctxt)]
      try (tactic.clear h)
      intro1
      let e ← intro1
      pure (e, ne_fail)
    | quote.1 ((%%ₓp) ∧ %%ₓq) => do
      mk_app `` And.elim_left [h ctxt] >>= lambdas ctxt >>= note data none
      let hq ← mk_app `` And.elim_right [h ctxt] >>= lambdas ctxt >>= note spec none
      try (tactic.clear h)
      pure (hq, none)
    | _ => fail "expected a term of the shape `∀xs, ∃a, p xs a` or `∀xs, p xs ∧ q xs`"

/-- Changes `(h : ∀xs, ∃as, p as ∧ q as) ⊢ g` to a list of functions `as`,
and a final hypothesis on `p as` and `q as`. If `nondep` is true then the functions will
be made to not depend on propositional arguments, when possible.

The last argument is an internal recursion variable, indicating whether nondep elimination
has been useful so far. The tactic fails if `nondep` is true, and nondep elimination is
attempted at least once, and it fails every time it is attempted, in which case it returns
an error complaining about the first attempt.
-/
unsafe def choose (nondep : Bool) : expr → List Name → optParam (Option (Option expr)) none → tactic Unit
  | h, [], _ => fail "expect list of variables"
  | h, [n], some (some Ne) => do
    let g ← mk_meta_var Ne
    set_goals [g]
    -- make a reasonable error state
        fail
        "choose: failed to synthesize nonempty instance"
  | h, [n], _ => do
    let cnt ← revert h
    intro n
    intron (cnt - 1)
    return ()
  | h, n :: ns, ne_fail₁ => do
    let (v, ne_fail₂) ← get_unused_name >>= choose1 nondep h n
    choose v ns <|
        match ne_fail₁, ne_fail₂ with
        | none, _ => ne_fail₂
        | some none, _ => some none
        | _, some none => some none
        | _, _ => ne_fail₁

namespace Interactive

setup_tactic_parser

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr *»
-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr ?»
/-- `choose a b h h' using hyp` takes an hypothesis `hyp` of the form
`∀ (x : X) (y : Y), ∃ (a : A) (b : B), P x y a b ∧ Q x y a b`
for some `P Q : X → Y → A → B → Prop` and outputs
into context a function `a : X → Y → A`, `b : X → Y → B` and two assumptions:
`h : ∀ (x : X) (y : Y), P x y (a x y) (b x y)` and
`h' : ∀ (x : X) (y : Y), Q x y (a x y) (b x y)`. It also works with dependent versions.

`choose! a b h h' using hyp` does the same, except that it will remove dependency of
the functions on propositional arguments if possible. For example if `Y` is a proposition
and `A` and `B` are nonempty in the above example then we will instead get
`a : X → A`, `b : X → B`, and the assumptions
`h : ∀ (x : X) (y : Y), P x y (a x) (b x)` and
`h' : ∀ (x : X) (y : Y), Q x y (a x) (b x)`.

Examples:

```lean
example (h : ∀n m : ℕ, ∃i j, m = n + i ∨ m + j = n) : true :=
begin
  choose i j h using h,
  guard_hyp i : ℕ → ℕ → ℕ,
  guard_hyp j : ℕ → ℕ → ℕ,
  guard_hyp h : ∀ (n m : ℕ), m = n + i n m ∨ m + j n m = n,
  trivial
end
```

```lean
example (h : ∀ i : ℕ, i < 7 → ∃ j, i < j ∧ j < i+i) : true :=
begin
  choose! f h h' using h,
  guard_hyp f : ℕ → ℕ,
  guard_hyp h : ∀ (i : ℕ), i < 7 → i < f i,
  guard_hyp h' : ∀ (i : ℕ), i < 7 → f i < i + i,
  trivial,
end
```
-/
unsafe def choose (nondep : parse («expr ?» (tk "!"))) (first : parse ident) (names : parse («expr *» ident))
    (tgt : parse («expr ?» (tk "using" *> texpr))) : tactic Unit := do
  let tgt ←
    match tgt with
      | none => get_local `this
      | some e => tactic.i_to_expr_strict e
  tactic.choose nondep tgt (first :: names)
  try (interactive.simp none none tt [simp_arg_type.expr (pquote.1 exists_prop)] [] (loc.ns <| some <$> names))
  try (tactic.clear tgt)

add_tactic_doc
  { Name := "choose", category := DocCategory.tactic, declNames := [`tactic.interactive.choose],
    tags := ["classical logic"] }

end Interactive

end Tactic

