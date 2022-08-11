/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Category.Basic

open CategoryTheory

-- TODO someone might like to generalise this tactic to work with other associative structures.
namespace Tactic

unsafe def repeat_with_results {α : Type} (t : tactic α) : tactic (List α) :=
  (do
      let r ← t
      let s ← repeat_with_results
      return (r :: s)) <|>
    return []

unsafe def repeat_count {α : Type} (t : tactic α) : tactic ℕ := do
  let r ← repeat_with_results t
  return r

end Tactic

namespace Conv

open Tactic

unsafe def repeat_with_results {α : Type} (t : tactic α) : tactic (List α) :=
  (do
      let r ← t
      let s ← repeat_with_results
      return (r :: s)) <|>
    return []

unsafe def repeat_count {α : Type} (t : tactic α) : tactic ℕ := do
  let r ← repeat_with_results t
  return r

unsafe def slice (a b : ℕ) : conv Unit := do
  repeat <| to_expr (pquote.1 Category.assoc) >>= fun e => tactic.rewrite_target e { symm := ff }
  iterate_range (a - 1) (a - 1) do
      conv.congr
      conv.skip
  let k ← repeat_count <| to_expr (pquote.1 Category.assoc) >>= fun e => tactic.rewrite_target e { symm := true }
  iterate_range (k + 1 + a - b) (k + 1 + a - b) conv.congr
  repeat <| to_expr (pquote.1 Category.assoc) >>= fun e => tactic.rewrite_target e { symm := ff }
  rotate 1
  iterate_exactly' (k + 1 + a - b) conv.skip

unsafe def slice_lhs (a b : ℕ) (t : conv Unit) : tactic Unit := do
  conv.interactive.to_lhs
  slice a b
  t

unsafe def slice_rhs (a b : ℕ) (t : conv Unit) : tactic Unit := do
  conv.interactive.to_rhs
  slice a b
  t

namespace Interactive

/-- `slice` is a conv tactic; if the current focus is a composition of several morphisms,
`slice a b` reassociates as needed, and zooms in on the `a`-th through `b`-th morphisms.

Thus if the current focus is `(a ≫ b) ≫ ((c ≫ d) ≫ e)`, then `slice 2 3` zooms to `b ≫ c`.
 -/
unsafe def slice :=
  conv.slice

end Interactive

end Conv

namespace Tactic

open Conv

private unsafe def conv_target' (c : conv Unit) : tactic Unit := do
  let t ← target
  let (new_t, pr) ← c.convert t
  replace_target new_t pr
  try tactic.triv
  try (tactic.reflexivity reducible)

namespace Interactive

setup_tactic_parser

/-- `slice_lhs a b { tac }` zooms to the left hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.
-/
unsafe def slice_lhs (a b : parse small_nat) (t : conv.interactive.itactic) : tactic Unit := do
  conv_target' ((conv.interactive.to_lhs >> slice a b) >> t)

/-- `slice_rhs a b { tac }` zooms to the right hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.
-/
unsafe def slice_rhs (a b : parse small_nat) (t : conv.interactive.itactic) : tactic Unit := do
  conv_target' ((conv.interactive.to_rhs >> slice a b) >> t)

end Interactive

end Tactic

/-- `slice_lhs a b { tac }` zooms to the left hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.

`slice_rhs a b { tac }` zooms to the right hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.
-/
add_tactic_doc
  { Name := "slice", category := DocCategory.tactic,
    declNames := [`tactic.interactive.slice_lhs, `tactic.interactive.slice_rhs], tags := ["category theory"] }

