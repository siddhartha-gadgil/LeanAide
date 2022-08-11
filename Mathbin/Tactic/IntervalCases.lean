/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Tactic.FinCases
import Mathbin.Data.Fin.Interval
import Mathbin.Data.Int.Interval
import Mathbin.Data.Pnat.Interval

/-!
# Case bash on variables in finite intervals

This file provides the tactic `interval_cases`. `interval_cases n` will:
1. inspect hypotheses looking for lower and upper bounds of the form `a ≤ n` and `n < b`
   (in `ℕ`, `ℤ`, `ℕ+`, bounds of the form `a < n` and `n ≤ b` are also allowed),
   and also makes use of lower and upper bounds found via `le_top` and `bot_le`
   (so for example if `n : ℕ`, then the bound `0 ≤ n` is automatically found).
2. call `fin_cases` on the synthesised hypothesis `n ∈ set.Ico a b`,
   assuming an appropriate `fintype` instance can be found for the type of `n`.

The variable `n` can belong to any type `α`, with the following restrictions:
* only bounds on which `expr.to_rat` succeeds will be considered "explicit" (TODO: generalise this?)
* an instance of `decidable_eq α` is available,
* an explicit lower bound can be found among the hypotheses, or from `bot_le n`,
* an explicit upper bound can be found among the hypotheses, or from `le_top n`,
* if multiple bounds are located, an instance of `linear_order α` is available, and
* an instance of `fintype set.Ico l u` is available for the relevant bounds.

You can also explicitly specify a lower and upper bound to use, as `interval_cases using hl hu`,
where the hypotheses should be of the form `hl : a ≤ n` and `hu : n < b`. In that case,
`interval_cases` calls `fin_cases` on the resulting hypothesis `h : n ∈ set.Ico a b`.
-/


-- These imports aren't required to compile this file,
-- These imports aren't required to compile this file,
-- but they are needed at the use site for the tactic to work
-- but they are needed at the use site for the tactic to work
-- (on values of type fin/int/pnat)
-- (on values of type fin/int/pnat)
open Set

namespace Tactic

namespace IntervalCases

/-- If `e` easily implies `(%%n < %%b)`
for some explicit `b`,
return that proof.
-/
-- We use `expr.to_rat` merely to decide if an `expr` is an explicit number.
-- It would be more natural to use `expr.to_int`, but that hasn't been implemented.
unsafe def gives_upper_bound (n e : expr) : tactic expr := do
  let t ← infer_type e
  match t with
    | quote.1 ((%%ₓn') < %%ₓb) => do
      guardₓ (n = n')
      let b ← b
      return e
    | quote.1 ((%%ₓb) > %%ₓn') => do
      guardₓ (n = n')
      let b ← b
      return e
    | quote.1 ((%%ₓn') ≤ %%ₓb) => do
      guardₓ (n = n')
      let b ← b
      let tn ← infer_type n
      match tn with
        | quote.1 ℕ => to_expr (pquote.1 (Nat.lt_add_one_iff.mpr (%%ₓe)))
        | quote.1 ℕ+ => to_expr (pquote.1 (Pnat.lt_add_one_iff.mpr (%%ₓe)))
        | quote.1 ℤ => to_expr (pquote.1 (Int.lt_add_one_iff.mpr (%%ₓe)))
        | _ => failed
    | quote.1 ((%%ₓb) ≥ %%ₓn') => do
      guardₓ (n = n')
      let b ← b
      let tn ← infer_type n
      match tn with
        | quote.1 ℕ => to_expr (pquote.1 (Nat.lt_add_one_iff.mpr (%%ₓe)))
        | quote.1 ℕ+ => to_expr (pquote.1 (Pnat.lt_add_one_iff.mpr (%%ₓe)))
        | quote.1 ℤ => to_expr (pquote.1 (Int.lt_add_one_iff.mpr (%%ₓe)))
        | _ => failed
    | _ => failed

/-- If `e` easily implies `(%%n ≥ %%b)`
for some explicit `b`,
return that proof.
-/
unsafe def gives_lower_bound (n e : expr) : tactic expr := do
  let t ← infer_type e
  match t with
    | quote.1 ((%%ₓn') ≥ %%ₓb) => do
      guardₓ (n = n')
      let b ← b
      return e
    | quote.1 ((%%ₓb) ≤ %%ₓn') => do
      guardₓ (n = n')
      let b ← b
      return e
    | quote.1 ((%%ₓn') > %%ₓb) => do
      guardₓ (n = n')
      let b ← b
      let tn ← infer_type n
      match tn with
        | quote.1 ℕ => to_expr (pquote.1 (Nat.add_one_le_iff.mpr (%%ₓe)))
        | quote.1 ℕ+ => to_expr (pquote.1 (Pnat.add_one_le_iff.mpr (%%ₓe)))
        | quote.1 ℤ => to_expr (pquote.1 (Int.add_one_le_iff.mpr (%%ₓe)))
        | _ => failed
    | quote.1 ((%%ₓb) < %%ₓn') => do
      guardₓ (n = n')
      let b ← b
      let tn ← infer_type n
      match tn with
        | quote.1 ℕ => to_expr (pquote.1 (Nat.add_one_le_iff.mpr (%%ₓe)))
        | quote.1 ℕ+ => to_expr (pquote.1 (Pnat.add_one_le_iff.mpr (%%ₓe)))
        | quote.1 ℤ => to_expr (pquote.1 (Int.add_one_le_iff.mpr (%%ₓe)))
        | _ => failed
    | _ => failed

/-- Combine two upper bounds. -/
unsafe def combine_upper_bounds : Option expr → Option expr → tactic (Option expr)
  | none, none => return none
  | some prf, none => return <| some prf
  | none, some prf => return <| some prf
  | some prf₁, some prf₂ => do
    Option.some <$> to_expr (pquote.1 (lt_minₓ (%%ₓprf₁) (%%ₓprf₂)))

/-- Combine two lower bounds. -/
unsafe def combine_lower_bounds : Option expr → Option expr → tactic (Option expr)
  | none, none => return <| none
  | some prf, none => return <| some prf
  | none, some prf => return <| some prf
  | some prf₁, some prf₂ => do
    Option.some <$> to_expr (pquote.1 (max_leₓ (%%ₓprf₂) (%%ₓprf₁)))

/-- Inspect a given expression, using it to update a set of upper and lower bounds on `n`. -/
unsafe def update_bounds (n : expr) (bounds : Option expr × Option expr) (e : expr) :
    tactic (Option expr × Option expr) := do
  let nlb ← try_core <| gives_lower_bound n e
  let nub ← try_core <| gives_upper_bound n e
  let clb ← combine_lower_bounds bounds.1 nlb
  let cub ← combine_upper_bounds bounds.2 nub
  return (clb, cub)

/-- Attempt to find a lower bound for the variable `n`, by evaluating `bot_le n`.
-/
unsafe def initial_lower_bound (n : expr) : tactic expr := do
  let e ← to_expr (pquote.1 (@bot_le _ _ _ (%%ₓn)))
  let t ← infer_type e
  match t with
    | quote.1 ((%%ₓb) ≤ %%ₓn) => do
      return e
    | _ => failed

/-- Attempt to find an upper bound for the variable `n`, by evaluating `le_top n`.
-/
unsafe def initial_upper_bound (n : expr) : tactic expr := do
  let e ← to_expr (pquote.1 (@le_top _ _ _ (%%ₓn)))
  match e with
    | quote.1 ((%%ₓn) ≤ %%ₓb) => do
      let tn ← infer_type n
      let e ←
        match tn with
          | quote.1 ℕ => to_expr (pquote.1 (Nat.add_one_le_iff.mpr (%%ₓe)))
          | quote.1 ℕ+ => to_expr (pquote.1 (Pnat.add_one_le_iff.mpr (%%ₓe)))
          | quote.1 ℤ => to_expr (pquote.1 (Int.add_one_le_iff.mpr (%%ₓe)))
          | _ => failed
      return e
    | _ => failed

/-- Inspect the local hypotheses for upper and lower bounds on a variable `n`. -/
unsafe def get_bounds (n : expr) : tactic (expr × expr) := do
  let hl ← try_core (initial_lower_bound n)
  let hu ← try_core (initial_upper_bound n)
  let lc ← local_context
  let r ← lc.mfoldl (update_bounds n) (hl, hu)
  match r with
    | (_, none) => fail "No upper bound located."
    | (none, _) => fail "No lower bound located."
    | (some lb_prf, some ub_prf) => return (lb_prf, ub_prf)

/-- The finset of elements of a set `s` for which we have `fintype s`. -/
def setElems {α} [DecidableEq α] (s : Set α) [Fintype s] : Finset α :=
  (Fintype.elems s).Image Subtype.val

/-- Each element of `s` is a member of `set_elems s`. -/
theorem mem_set_elems {α} [DecidableEq α] (s : Set α) [Fintype s] {a : α} (h : a ∈ s) : a ∈ setElems s :=
  Finset.mem_image.2 ⟨⟨a, h⟩, Fintype.complete _, rfl⟩

end IntervalCases

open IntervalCases

/-- Call `fin_cases` on membership of the finset built from
an `Ico` interval corresponding to a lower and an upper bound.

Here `hl` should be an expression of the form `a ≤ n`, for some explicit `a`, and
`hu` should be of the form `n < b`, for some explicit `b`.

By default `interval_cases_using` automatically generates a name for the new hypothesis. The name
can be specified via the optional argument `n`.
-/
unsafe def interval_cases_using (hl hu : expr) (n : Option Name) : tactic Unit :=
  (to_expr (pquote.1 (mem_set_elems (Ico _ _) ⟨%%ₓhl, %%ₓhu⟩)) >>=
      if hn : n.isSome then note (Option.getₓ hn) else note_anon none) >>=
    fin_cases_at none none

setup_tactic_parser

namespace Interactive

-- mathport name: «expr ?»
local postfix:1024 "?" => optionalₓ

/-- `interval_cases n` searches for upper and lower bounds on a variable `n`,
and if bounds are found,
splits into separate cases for each possible value of `n`.

As an example, in
```
example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
begin
  interval_cases n,
  all_goals {simp}
end
```
after `interval_cases n`, the goals are `3 = 3 ∨ 3 = 4` and `4 = 3 ∨ 4 = 4`.

You can also explicitly specify a lower and upper bound to use,
as `interval_cases using hl hu`.
The hypotheses should be in the form `hl : a ≤ n` and `hu : n < b`,
in which case `interval_cases` calls `fin_cases` on the resulting fact `n ∈ set.Ico a b`.

You can specify a name `h` for the new hypothesis,
as `interval_cases n with h` or `interval_cases n using hl hu with h`.
-/
unsafe def interval_cases (n : parse texpr ?) (bounds : parse (tk "using" *> (Prod.mk <$> ident <*> ident))?)
    (lname : parse (tk "with" *> ident)?) : tactic Unit := do
  if h : n then do
      guardₓ bounds <|> fail "Do not use the `using` keyword if specifying the variable explicitly."
      let n ← to_expr (Option.getₓ h)
      let (hl, hu) ← get_bounds n
      tactic.interval_cases_using hl hu lname
    else
      if h' : bounds then do
        let [hl, hu] ← [(Option.getₓ h').1, (Option.getₓ h').2].mmap get_local
        tactic.interval_cases_using hl hu lname
      else
        fail
          ("Call `interval_cases n` (specifying a variable), or `interval_cases lb ub`\n" ++
            "(specifying a lower bound and upper bound on the same variable).")

/-- `interval_cases n` searches for upper and lower bounds on a variable `n`,
and if bounds are found,
splits into separate cases for each possible value of `n`.

As an example, in
```
example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 :=
begin
  interval_cases n,
  all_goals {simp}
end
```
after `interval_cases n`, the goals are `3 = 3 ∨ 3 = 4` and `4 = 3 ∨ 4 = 4`.

You can also explicitly specify a lower and upper bound to use,
as `interval_cases using hl hu`.
The hypotheses should be in the form `hl : a ≤ n` and `hu : n < b`,
in which case `interval_cases` calls `fin_cases` on the resulting fact `n ∈ set.Ico a b`.

You can also explicitly specify a name to use for the hypothesis added,
as `interval_cases n with hn` or `interval_cases n using hl hu with hn`.

In particular, `interval_cases n`
1) inspects hypotheses looking for lower and upper bounds of the form `a ≤ n` and `n < b`
   (although in `ℕ`, `ℤ`, and `ℕ+` bounds of the form `a < n` and `n ≤ b` are also allowed),
   and also makes use of lower and upper bounds found via `le_top` and `bot_le`
   (so for example if `n : ℕ`, then the bound `0 ≤ n` is found automatically), then
2) calls `fin_cases` on the synthesised hypothesis `n ∈ set.Ico a b`,
   assuming an appropriate `fintype` instance can be found for the type of `n`.

The variable `n` can belong to any type `α`, with the following restrictions:
* only bounds on which `expr.to_rat` succeeds will be considered "explicit" (TODO: generalise this?)
* an instance of `decidable_eq α` is available,
* an explicit lower bound can be found amongst the hypotheses, or from `bot_le n`,
* an explicit upper bound can be found amongst the hypotheses, or from `le_top n`,
* if multiple bounds are located, an instance of `linear_order α` is available, and
* an instance of `fintype set.Ico l u` is available for the relevant bounds.
-/
add_tactic_doc
  { Name := "interval_cases", category := DocCategory.tactic, declNames := [`tactic.interactive.interval_cases],
    tags := ["case bashing"] }

end Interactive

end Tactic

