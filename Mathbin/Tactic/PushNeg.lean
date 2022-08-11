/-
Copyright (c) 2019 Patrick Massot All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Simon Hudon

A tactic pushing negations into an expression
-/
import Mathbin.Logic.Basic

open Tactic Expr

namespace PushNeg

section

universe u

variable {α : Sort u}

variable (p q : Prop)

variable (s : α → Prop)

attribute [local instance] Classical.propDecidable

theorem not_not_eq : (¬¬p) = p :=
  propext not_not

theorem not_and_eq : (¬(p ∧ q)) = (p → ¬q) :=
  propext not_and

theorem not_or_eq : (¬(p ∨ q)) = (¬p ∧ ¬q) :=
  propext not_or_distrib

theorem not_forall_eq : (¬∀ x, s x) = ∃ x, ¬s x :=
  propext not_forall

theorem not_exists_eq : (¬∃ x, s x) = ∀ x, ¬s x :=
  propext not_exists

theorem not_implies_eq : (¬(p → q)) = (p ∧ ¬q) :=
  propext not_imp

theorem Classical.implies_iff_not_or : p → q ↔ ¬p ∨ q :=
  imp_iff_not_or

theorem not_eq (a b : α) : ¬a = b ↔ a ≠ b :=
  Iff.rfl

variable {β : Type u}

variable [LinearOrderₓ β]

theorem not_le_eq (a b : β) : (¬a ≤ b) = (b < a) :=
  propext not_leₓ

theorem not_lt_eq (a b : β) : (¬a < b) = (b ≤ a) :=
  propext not_ltₓ

end

unsafe def whnf_reducible (e : expr) : tactic expr :=
  whnf e reducible

private unsafe def transform_negation_step (e : expr) : tactic (Option (expr × expr)) := do
  let e ← whnf_reducible e
  match e with
    | quote.1 ¬%%ₓNe => do
      let ne ← whnf_reducible Ne
      match Ne with
        | quote.1 ¬%%ₓa => do
          let pr ← mk_app `` not_not_eq [a]
          return (some (a, pr))
        | quote.1 ((%%ₓa) ∧ %%ₓb) => do
          let pr ← mk_app `` not_and_eq [a, b]
          return (some (quote.1 ((%%ₓa : Prop) → ¬%%ₓb), pr))
        | quote.1 ((%%ₓa) ∨ %%ₓb) => do
          let pr ← mk_app `` not_or_eq [a, b]
          return (some (quote.1 ((¬%%ₓa) ∧ ¬%%ₓb), pr))
        | quote.1 ((%%ₓa) ≤ %%ₓb) => do
          let e ← to_expr (pquote.1 ((%%ₓb) < %%ₓa))
          let pr ← mk_app `` not_le_eq [a, b]
          return (some (e, pr))
        | quote.1 ((%%ₓa) < %%ₓb) => do
          let e ← to_expr (pquote.1 ((%%ₓb) ≤ %%ₓa))
          let pr ← mk_app `` not_lt_eq [a, b]
          return (some (e, pr))
        | quote.1 (Exists (%%ₓp)) => do
          let pr ← mk_app `` not_exists_eq [p]
          let e ←
            match p with
              | lam n bi typ bo => do
                let body ← mk_app `` Not [bo]
                return (pi n bi typ body)
              | _ => tactic.fail "Unexpected failure negating ∃"
          return (some (e, pr))
        | pi n bi d p =>
          if p then do
            let pr ← mk_app `` not_forall_eq [lam n bi d p]
            let body ← mk_app `` Not [p]
            let e ← mk_app `` Exists [lam n bi d body]
            return (some (e, pr))
          else do
            let pr ← mk_app `` not_implies_eq [d, p]
            let quote.1 ((%%ₓ_) = %%ₓe') ← infer_type pr
            return (some (e', pr))
        | _ => return none
    | _ => return none

private unsafe def transform_negation : expr → tactic (Option (expr × expr))
  | e => do
    let some (e', pr) ← transform_negation_step e | return none
    let some (e'', pr') ← transform_negation e' | return (some (e', pr))
    let pr'' ← mk_eq_trans pr pr'
    return (some (e'', pr''))

unsafe def normalize_negations (t : expr) : tactic (expr × expr) := do
  let (_, e, pr) ←
    simplify_top_down ()
        (fun _ => fun e => do
          let oepr ← transform_negation e
          match oepr with
            | some (e', pr) => return ((), e', pr)
            | none => do
              let pr ← mk_eq_refl e
              return ((), e, pr))
        t { eta := false }
  return (e, pr)

unsafe def push_neg_at_hyp (h : Name) : tactic Unit := do
  let H ← get_local h
  let t ← infer_type H
  let (e, pr) ← normalize_negations t
  replace_hyp H e pr
  skip

unsafe def push_neg_at_goal : tactic Unit := do
  let H ← target
  let (e, pr) ← normalize_negations H
  replace_target e pr

end PushNeg

open Interactive (parse loc.ns loc.wildcard)

open Interactive.Types (location texpr)

open Lean.Parser (tk ident many)

open Interactive.Loc

-- mathport name: «expr ?»
local postfix:1024 "?" => optionalₓ

-- mathport name: «expr *»
local postfix:1024 "*" => many

open PushNeg

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- Push negations in the goal of some assumption.

For instance, a hypothesis `h : ¬ ∀ x, ∃ y, x ≤ y` will be transformed by `push_neg at h` into
`h : ∃ x, ∀ y, y < x`. Variables names are conserved.

This tactic pushes negations inside expressions. For instance, given an assumption
```lean
h : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε)
```
writing `push_neg at h` will turn `h` into
```lean
h : ∃ ε, ε > 0 ∧ ∀ δ, δ > 0 → (∃ x, |x - x₀| ≤ δ ∧ ε < |f x - y₀|),
```

(the pretty printer does *not* use the abreviations `∀ δ > 0` and `∃ ε > 0` but this issue
has nothing to do with `push_neg`).
Note that names are conserved by this tactic, contrary to what would happen with `simp`
using the relevant lemmas. One can also use this tactic at the goal using `push_neg`,
at every assumption and the goal using `push_neg at *` or at selected assumptions and the goal
using say `push_neg at h h' ⊢` as usual.
-/
unsafe def tactic.interactive.push_neg : parse location → tactic Unit
  | loc.ns loc_l =>
    loc_l.mmap' fun l =>
      match l with
      | some h => do
        push_neg_at_hyp h
        try <|
            interactive.simp_core { eta := ff } failed tt [simp_arg_type.expr (pquote.1 PushNeg.not_eq)] []
              (Interactive.Loc.ns [some h])
      | none => do
        push_neg_at_goal
        try sorry
  | loc.wildcard => do
    push_neg_at_goal
    local_context >>= mmap' fun h => push_neg_at_hyp (local_pp_name h)
    try sorry

add_tactic_doc
  { Name := "push_neg", category := DocCategory.tactic, declNames := [`tactic.interactive.push_neg], tags := ["logic"] }

theorem imp_of_not_imp_not (P Q : Prop) : (¬Q → ¬P) → P → Q := fun h hP => Classical.by_contradiction fun h' => h h' hP

/-- Matches either an identifier "h" or a pair of identifiers "h with k" -/
unsafe def name_with_opt : lean.parser (Name × Option Name) :=
  Prod.mk <$> ident <*> (some <$> (tk "with" *> ident) <|> return none)

/-- Transforms the goal into its contrapositive.

* `contrapose`     turns a goal `P → Q` into `¬ Q → ¬ P`
* `contrapose!`    turns a goal `P → Q` into `¬ Q → ¬ P` and pushes negations inside `P` and `Q`
  using `push_neg`
* `contrapose h`   first reverts the local assumption `h`, and then uses `contrapose` and `intro h`
* `contrapose! h`  first reverts the local assumption `h`, and then uses `contrapose!` and `intro h`
* `contrapose h with new_h` uses the name `new_h` for the introduced hypothesis
-/
unsafe def tactic.interactive.contrapose (push : parse (tk "!")?) : parse name_with_opt ? → tactic Unit
  | some (h, h') => (((get_local h >>= revert) >> tactic.interactive.contrapose none) >> intro (h'.getOrElse h)) >> skip
  | none => do
    let quote.1 ((%%ₓP) → %%ₓQ) ← target | fail "The goal is not an implication, and you didn't specify an assumption"
    let cp ←
      mk_mapp `` imp_of_not_imp_not [P, Q] <|> fail "contrapose only applies to nondependent arrows between props"
    apply cp
    when push <| try (tactic.interactive.push_neg (loc.ns [none]))

add_tactic_doc
  { Name := "contrapose", category := DocCategory.tactic, declNames := [`tactic.interactive.contrapose],
    tags := ["logic"] }

