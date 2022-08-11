/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Patrick Massot
-/
import Mathbin.Tactic.Monotonicity.Default

namespace Tactic

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Apply the function `f` given by `e : pexpr` to the local hypothesis `hyp`, which must either be
of the form `a = b` or `a ≤ b`, replacing the type of `hyp` with `f a = f b` or `f a ≤ f b`. If
`hyp` names an inequality then a new goal `monotone f` is created, unless the name of a proof of
this fact is passed as the optional argument `mono_lem`, or the `mono` tactic can prove it.
-/
unsafe def apply_fun_to_hyp (e : pexpr) (mono_lem : Option pexpr) (hyp : expr) : tactic Unit := do
  let t ← infer_type hyp >>= instantiate_mvars
  let prf ←
    match t with
      | quote.1 ((%%ₓl) = %%ₓr) => do
        let ltp ← infer_type l
        let mv ← mk_mvar
        to_expr (pquote.1 (congr_arg (%%ₓe : (%%ₓltp) → %%ₓmv) (%%ₓhyp)))
      | quote.1 ((%%ₓl) ≤ %%ₓr) => do
        let Hmono ←
          match mono_lem with
            | some mono_lem => tactic.i_to_expr mono_lem
            | none => do
              let n ← get_unused_name `mono
              to_expr (pquote.1 (Monotone (%%ₓe))) >>= assert n
              -- In order to resolve implicit arguments in `%%e`,
                -- we build (and discard) the expression `%%n %%hyp` before calling the `mono` tactic.
                swap
              let n ← get_local n
              to_expr (pquote.1 ((%%ₓn) (%%ₓhyp)))
              swap
              (do
                    intro_lst [`x, `y, `h]
                    sorry) <|>
                  swap
              return n
        to_expr (pquote.1 ((%%ₓHmono) (%%ₓhyp)))
      | _ =>
        "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
  clear hyp
  let hyp ← note hyp.local_pp_name none prf
  -- let's try to force β-reduction at `h`
      try <|
      tactic.dsimp_hyp hyp simp_lemmas.mk [] { eta := False, beta := True }

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Attempt to "apply" a function `f` represented by the argument `e : pexpr` to the goal.

If the goal is of the form `a ≠ b`, we obtain the new goal `f a ≠ f b`.
If the goal is of the form `a = b`, we obtain a new goal `f a = f b`, and a subsidiary goal
`injective f`.
(We attempt to discharge this subsidiary goal automatically, or using the optional argument.)
If the goal is of the form `a ≤ b` (or similarly for `a < b`), and `f` is an `order_iso`,
we obtain a new goal `f a ≤ f b`.
-/
unsafe def apply_fun_to_goal (e : pexpr) (lem : Option pexpr) : tactic Unit := do
  let t ← target
  match t with
    | quote.1 ((%%ₓl) ≠ %%ₓr) => (to_expr (pquote.1 (ne_of_apply_ne (%%ₓe))) >>= apply) >> skip
    | quote.1 ¬(%%ₓl) = %%ₓr => (to_expr (pquote.1 (ne_of_apply_ne (%%ₓe))) >>= apply) >> skip
    | quote.1 ((%%ₓl) ≤ %%ₓr) => (to_expr (pquote.1 (OrderIso.le_iff_le (%%ₓe)).mp) >>= apply) >> skip
    | quote.1 ((%%ₓl) < %%ₓr) => (to_expr (pquote.1 (OrderIso.lt_iff_lt (%%ₓe)).mp) >>= apply) >> skip
    | quote.1 ((%%ₓl) = %%ₓr) =>
      focus1 do
        to_expr (pquote.1 ((%%ₓe) (%%ₓl)))
        let n
          ←-- build and discard an application, to fill in implicit arguments
              get_unused_name
              `inj
        to_expr (pquote.1 (Function.Injective (%%ₓe))) >>= assert n
        (-- Attempt to discharge the `injective f` goal
              -- We require that applying the lemma closes the goal, not just makes progress:
              focus1 <|
              assumption <|>
                (to_expr (pquote.1 Equivₓ.injective) >>= apply) >> done <|>
                  (lem fun l => to_expr l >>= apply) >> done) <|>
            swap
        let n
          ←-- return to the main goal if we couldn't discharge `injective f`.
              get_local
              n
        apply n
        clear n
    | _ =>
      "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"

namespace Interactive

setup_tactic_parser

/-- Apply a function to an equality or inequality in either a local hypothesis or the goal.

* If we have `h : a = b`, then `apply_fun f at h` will replace this with `h : f a = f b`.
* If we have `h : a ≤ b`, then `apply_fun f at h` will replace this with `h : f a ≤ f b`,
  and create a subsidiary goal `monotone f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using `mono`,
  or an explicit solution can be provided with `apply_fun f at h using P`, where `P : monotone f`.
* If the goal is `a ≠ b`, `apply_fun f` will replace this with `f a ≠ f b`.
* If the goal is `a = b`, `apply_fun f` will replace this with `f a = f b`,
  and create a subsidiary goal `injective f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using local hypotheses,
  or if `f` is actually an `equiv`,
  or an explicit solution can be provided with `apply_fun f using P`, where `P : injective f`.
* If the goal is `a ≤ b` (or similarly for `a < b`), and `f` is actually an `order_iso`,
  `apply_fun f` will replace the goal with `f a ≤ f b`.
  If `f` is anything else (e.g. just a function, or an `equiv`), `apply_fun` will fail.


Typical usage is:
```lean
open function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : injective $ g ∘ f) :
  injective f :=
begin
  intros x x' h,
  apply_fun g at h,
  exact H h
end
```
 -/
unsafe def apply_fun (q : parse texpr) (locs : parse location) (lem : parse (tk "using" *> texpr)?) : tactic Unit :=
  locs.apply (apply_fun_to_hyp q lem) (apply_fun_to_goal q lem)

add_tactic_doc
  { Name := "apply_fun", category := DocCategory.tactic, declNames := [`tactic.interactive.apply_fun],
    tags := ["context management"] }

end Interactive

end Tactic

