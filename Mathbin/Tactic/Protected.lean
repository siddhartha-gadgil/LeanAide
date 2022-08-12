/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.Tactic.Core

/-!
## `protected` and `protect_proj` user attributes

`protected` is an attribute to protect a declaration.
If a declaration `foo.bar` is marked protected, then it must be referred to
by its full name `foo.bar`, even when the `foo` namespace is open.

`protect_proj` attribute to protect the projections of a structure.
If a structure `foo` is marked with the `protect_proj` user attribute, then
all of the projections become protected.

`protect_proj without bar baz` will protect all projections except for `bar` and `baz`.

# Examples

In this example all of `foo.bar`, `foo.baz` and `foo.qux` will be protected.
```
@[protect_proj] structure foo : Type :=
(bar : unit) (baz : unit) (qux : unit)
```

The following code example define the structure `foo`, and the projections `foo.qux`
will be protected, but not `foo.baz` or `foo.bar`

```
@[protect_proj without baz bar] structure foo : Type :=
(bar : unit) (baz : unit) (qux : unit)
```
-/


namespace Tactic

/-- Attribute to protect a declaration.
If a declaration `foo.bar` is marked protected, then it must be referred to
by its full name `foo.bar`, even when the `foo` namespace is open.

Protectedness is a built in parser feature that is independent of this attribute.
A declaration may be protected even if it does not have the `@[protected]` attribute.
This provides a convenient way to protect many declarations at once.
-/
@[user_attribute]
unsafe def protected_attr : user_attribute where
  Name := "protected"
  descr :=
    "Attribute to protect a declaration\n    If a declaration `foo.bar` is marked protected, then it must be referred to\n    by its full name `foo.bar`, even when the `foo` namespace is open."
  after_set := some fun n _ _ => mk_protected n

add_tactic_doc
  { Name := "protected", category := DocCategory.attr, declNames := [`tactic.protected_attr],
    tags := ["parsing", "environment"] }

/-- Tactic that is executed when a structure is marked with the `protect_proj` attribute -/
unsafe def protect_proj_tac (n : Name) (l : List Name) : tactic Unit := do
  let env ← get_env
  match env n with
    | none => fail "protect_proj failed: declaration is not a structure"
    | some fields => fields fun field => when (l fun m => bnot <| m field) <| mk_protected field

/-- Attribute to protect the projections of a structure.
If a structure `foo` is marked with the `protect_proj` user attribute, then
all of the projections become protected, meaning they must always be referred to by
their full name `foo.bar`, even when the `foo` namespace is open.

`protect_proj without bar baz` will protect all projections except for `bar` and `baz`.

```lean
@[protect_proj without baz bar] structure foo : Type :=
(bar : unit) (baz : unit) (qux : unit)
```
-/
@[user_attribute]
unsafe def protect_proj_attr : user_attribute Unit (List Name) where
  Name := "protect_proj"
  descr :=
    "Attribute to protect the projections of a structure.\n    If a structure `foo` is marked with the `protect_proj` user attribute, then\n    all of the projections become protected, meaning they must always be referred to by\n    their full name `foo.bar`, even when the `foo` namespace is open.\n\n    `protect_proj without bar baz` will protect all projections except for bar and baz"
  after_set :=
    some fun n _ _ => do
      let l ← protect_proj_attr.get_param n
      protect_proj_tac n l
  parser := interactive.types.without_ident_list

add_tactic_doc
  { Name := "protect_proj", category := DocCategory.attr, declNames := [`tactic.protect_proj_attr],
    tags := ["parsing", "environment", "structures"] }

end Tactic

