/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathbin.Tactic.Interactive

/-!
# Rename bound variable tactic

This files defines a tactic `rename_var` whose main purpose is to teach
renaming of bound variables.

* `rename_var old new` renames all bound variables named `old` to `new` in the goal.
* `rename_var old new at h` does the same in hypothesis `h`.

```lean
example (P : ℕ →  ℕ → Prop) (h : ∀ n, ∃ m, P n m) : ∀ l, ∃ m, P l m :=
begin
  rename_var n q at h, -- h is now ∀ (q : ℕ), ∃ (m : ℕ), P q m,
  rename_var m n, -- goal is now ∀ (l : ℕ), ∃ (n : ℕ), P k n,
  exact h -- Lean does not care about those bound variable names
end
```

## Tags

teaching, tactic
-/


open Expr

/-- Rename bound variable `old` to `new` in an `expr`-/
unsafe def expr.rename_var (old new : Name) : expr → expr
  | pi n bi t b => pi (if n = old then new else n) bi (expr.rename_var t) (expr.rename_var b)
  | lam n bi t b => lam (if n = old then new else n) bi (expr.rename_var t) (expr.rename_var b)
  | app t b => app (expr.rename_var t) (expr.rename_var b)
  | e => e

namespace Tactic

/-- Rename bound variable `old` to `new` in goal -/
unsafe def rename_var_at_goal (old new : Name) : tactic Unit := do
  let old_tgt ← target
  tactic.change (expr.rename_var old new old_tgt)

/-- Rename bound variable `old` to `new` in assumption `h` -/
unsafe def rename_var_at_hyp (old new : Name) (e : expr) : tactic Unit := do
  let old_e ← infer_type e
  tactic.change_core (expr.rename_var old new old_e) (some e)

end Tactic

namespace Tactic.Interactive

open Tactic

setup_tactic_parser

/-- `rename_var old new` renames all bound variables named `old` to `new` in the goal.
`rename_var old new at h` does the same in hypothesis `h`.
-/
unsafe def rename_var (old : parse ident) (new : parse ident) (l : parse location) : tactic Unit :=
  l.apply (rename_var_at_hyp old new) (rename_var_at_goal old new)

end Tactic.Interactive

/-- `rename_var old new` renames all bound variables named `old` to `new` in the goal.
`rename_var old new at h` does the same in hypothesis `h`.
This is meant for teaching bound variables only. Such a renaming should never be relevant to Lean.

```lean
example (P : ℕ →  ℕ → Prop) (h : ∀ n, ∃ m, P n m) : ∀ l, ∃ m, P l m :=
begin
  rename_var n q at h, -- h is now ∀ (q : ℕ), ∃ (m : ℕ), P q m,
  rename_var m n, -- goal is now ∀ (l : ℕ), ∃ (n : ℕ), P k n,
  exact h -- Lean does not care about those bound variable names
end
```
-/
add_tactic_doc
  { Name := "rename_var", category := DocCategory.tactic, declNames := [`tactic.interactive.rename_var],
    tags := ["renaming"] }

