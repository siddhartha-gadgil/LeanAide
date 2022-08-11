/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Mathbin.Tactic.Core

/-!
# A tactic for type-based naming of variables

When we name hypotheses or variables, we often do so in a type-directed fashion:
a hypothesis of type `ℕ` is called `n` or `m`; a hypothesis of type `list ℕ` is
called `ns`; etc. This module provides a tactic,
`tactic.typical_variable_names`, which looks up typical variable names for a
given type.

Typical variable names are registered by giving an instance of the type class
`has_variable_names`. This file provides `has_variable_names` instances for many
of the core Lean types. If you want to override these, you can declare a
high-priority instance (perhaps localised) of `has_variable_names`. E.g. to
change the names given to natural numbers:

```lean
def foo : has_variable_names ℕ :=
⟨[`i, `j, `k]⟩

local attribute [instance, priority 1000] foo
```
-/


universe u v

/-- Type class for associating a type `α` with typical variable names for elements
of `α`. See `tactic.typical_variable_names`.
-/
class HasVariableNames (α : Sort u) : Type where
  names : List Name
  names_nonempty : 0 < names.length := by
    run_tac
      tactic.exact_dec_trivial

namespace Tactic

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- `typical_variable_names t` obtains typical names for variables of type `t`.
The returned list is guaranteed to be nonempty. Fails if there is no instance
`has_typical_variable_names t`.

```
typical_variable_names `(ℕ) = [`n, `m, `o]
```
-/
unsafe def typical_variable_names (t : expr) : tactic (List Name) :=
  (do
      let names ← to_expr (pquote.1 (HasVariableNames.names (%%ₓt)))
      eval_expr (List Name) names) <|>
    "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"

end Tactic

namespace HasVariableNames

/-- `@make_listlike_instance α _ β` creates an instance `has_variable_names β` from
an instance `has_variable_names α`. If `α` has associated names `a`, `b`, ...,
the generated instance for `β` has names `as`, `bs`, ... This can be used to
create instances for 'containers' such as lists or sets.
-/
def makeListlikeInstance (α : Sort u) [HasVariableNames α] {β : Sort v} : HasVariableNames β :=
  ⟨(names α).map fun n => n.appendSuffix "s", by
    simp [← names_nonempty]⟩

/-- `@make_inheriting_instance α _ β` creates an instance `has_variable_names β`
from an instance `has_variable_names α`. The generated instance contains the
same variable names as that of `α`. This can be used to create instances for
'wrapper' types like `option` and `subtype`.
-/
def makeInheritingInstance (α : Sort u) [HasVariableNames α] {β : Sort v} : HasVariableNames β :=
  ⟨names α, names_nonempty⟩

end HasVariableNames

open HasVariableNames

instance {n α} [HasVariableNames α] : HasVariableNames (DArray n fun _ => α) :=
  makeListlikeInstance α

instance : HasVariableNames Bool :=
  ⟨[`b]⟩

instance : HasVariableNames Charₓ :=
  ⟨[`c]⟩

instance {n} : HasVariableNames (Finₓ n) :=
  ⟨[`n, `m, `o]⟩

instance : HasVariableNames ℤ :=
  ⟨[`n, `m, `o]⟩

instance {α} [HasVariableNames α] : HasVariableNames (List α) :=
  makeListlikeInstance α

instance : HasVariableNames ℕ :=
  ⟨[`n, `m, `o]⟩

instance Prop.hasVariableNames : HasVariableNames Prop :=
  ⟨[`P, `Q, `R]⟩

instance {α} [HasVariableNames α] : HasVariableNames (Thunkₓ α) :=
  makeInheritingInstance α

instance {α β} : HasVariableNames (Prod α β) :=
  ⟨[`p]⟩

instance {α β} : HasVariableNames (PProd α β) :=
  ⟨[`p]⟩

instance {α} {β : α → Type _} : HasVariableNames (Sigma β) :=
  ⟨[`p]⟩

instance {α} {β : α → Sort _} : HasVariableNames (PSigma β) :=
  ⟨[`p]⟩

instance {α} [HasVariableNames α] {p : α → Prop} : HasVariableNames (Subtype p) :=
  makeInheritingInstance α

instance {α} [HasVariableNames α] : HasVariableNames (Option α) :=
  makeInheritingInstance α

instance {α} : HasVariableNames (BinTree α) :=
  ⟨[`t]⟩

instance {α} [HasVariableNames α] {lt : α → α → Prop} : HasVariableNames (Rbtree α lt) :=
  makeListlikeInstance α

unsafe instance {α} [HasVariableNames α] : HasVariableNames (native.rb_set α) :=
  makeListlikeInstance α

instance {α} [HasVariableNames α] : HasVariableNames (Set α) :=
  makeListlikeInstance α

instance : HasVariableNames Stringₓ :=
  ⟨[`s]⟩

instance : HasVariableNames Unsigned :=
  ⟨[`n, `m, `o]⟩

instance {α} {β : α → Sort _} : HasVariableNames (∀ a : α, β a) :=
  ⟨[`f, `g, `h]⟩

instance : HasVariableNames Name :=
  ⟨[`n]⟩

unsafe instance {α} : HasVariableNames (tactic α) :=
  ⟨[`t]⟩

unsafe instance : HasVariableNames expr :=
  ⟨[`e]⟩

unsafe instance : HasVariableNames pexpr :=
  ⟨[`e]⟩

unsafe instance : HasVariableNames level :=
  ⟨[`u, `v, `w]⟩

instance : HasVariableNames BinderInfo :=
  ⟨[`bi]⟩

