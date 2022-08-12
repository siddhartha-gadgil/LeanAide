/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Mathbin.Meta.RbMap
import Mathbin.Tactic.Core

/-!
# Tactics About Dependencies

This module provides tactics to compute dependencies and reverse dependencies of
hypotheses. An expression `e` depends on a hypothesis `h` if `e` would not be
valid if `h` were removed from the context. For example, the expression
`e := x > 0` depends on `x`. We say that `x` is a dependency of `e` and that `e`
is a reverse dependency of `x`.

It is sometimes useful to consider *inclusive* dependency: `e` inclusively
depends on `h` iff `e` depends on `h` or `e = h` (so inclusive dependency is the
reflexive closure of regular dependency).

Note that the standard library does not use quite the same terminology:

* `kdependencies`/`kdeps` from the standard library compute reverse
  dependencies, not dependencies.
* `kdepends_on` and functions derived from it ignore local definitions and
  therefore compute a weaker dependency relation (see next section).

## Local Definitions

Determining dependencies of hypotheses is usually straightforward: a hypothesis
`r : R` depends on another hypothesis `d : D` if `d` occurs in `R`. The
implementation is more involved, however, in the presence of local definitions.
Consider this context:

```lean
n m : ℕ
k : ℕ := m
o : ℕ := k
h : o > 0
```

`h` depends on `o`, `k` and `m`, but only the dependency on `o` is syntactically
obvious. `kdepends_on` ignores this complication and claims that `h` does not
depend on `k` or `m`. We do not follow this example but process local
definitions properly. This means that if the context contains a local
definition, we need to compute the syntactic dependencies of `h`, then their
dependencies, and so on.

## Direct Dependencies

If you want to ignore local definitions while computing dependencies, this
module also provides tactics to find the *direct* dependencies of a hypothesis.
These are the hypotheses that syntactically appear in the hypothesis's type (or
value, if the hypothesis is a local definition).
-/


open Native

open ExprSet (local_set_to_name_set)

open NameSet (local_list_to_name_set)

namespace Tactic

/-! ### Direct Dependencies -/


/-! #### Checking whether hypotheses directly depend on each other -/


/-- `type_has_local_in_name_set h ns` returns true iff the type of `h` contains a
local constant whose unique name appears in `ns`.
-/
unsafe def type_has_local_in_name_set (h : expr) (ns : name_set) : tactic Bool := do
  let h_type ← infer_type h
  pure <| h_type ns

/-- `type_has_local_in_set h hs` returns true iff the type of `h` contains any of
the local constants `hs`.
-/
unsafe def type_has_local_in_set (h : expr) (hs : expr_set) : tactic Bool :=
  type_has_local_in_name_set h <| local_set_to_name_set hs

/-- `type_has_local_in h hs` returns true iff the type of `h` contains any of the
local constants `hs`.
-/
unsafe def type_has_local_in (h : expr) (hs : List expr) : tactic Bool :=
  type_has_local_in_name_set h <| local_list_to_name_set hs

/-- `local_def_value_has_local_in_name_set h ns` returns true iff `h` is a local
definition whose value contains a local constant whose unique name appears in
`ns`.
-/
unsafe def local_def_value_has_local_in_name_set (h : expr) (ns : name_set) : tactic Bool := do
  let some h_val ← try_core <| local_def_value h | pure false
  pure <| h_val ns

/-- `local_def_value_has_local_in_set h hs` returns true iff `h` is a local
definition whose value contains any of the local constants `hs`.
-/
unsafe def local_def_value_has_local_in_set (h : expr) (hs : expr_set) : tactic Bool :=
  local_def_value_has_local_in_name_set h <| local_set_to_name_set hs

/-- `local_def_value_has_local_in h hs` returns true iff `h` is a local definition
whose value contains any of the local constants `hs`.
-/
unsafe def local_def_value_has_local_in (h : expr) (hs : List expr) : tactic Bool :=
  local_def_value_has_local_in_name_set h <| local_list_to_name_set hs

/-- `hyp_directly_depends_on_local_name_set h ns` is true iff the hypothesis `h`
directly depends on a hypothesis whose unique name appears in `ns`.
-/
unsafe def hyp_directly_depends_on_local_name_set (h : expr) (ns : name_set) : tactic Bool :=
  List.mbor [type_has_local_in_name_set h ns, local_def_value_has_local_in_name_set h ns]

/-- `hyp_directly_depends_on_local_set h hs` is true iff the hypothesis `h` directly
depends on any of the hypotheses `hs`.
-/
unsafe def hyp_directly_depends_on_local_set (h : expr) (hs : expr_set) : tactic Bool :=
  hyp_directly_depends_on_local_name_set h <| local_set_to_name_set hs

/-- `hyp_directly_depends_on_locals h hs` is true iff the hypothesis `h` directly
depends on any of the hypotheses `hs`.
-/
unsafe def hyp_directly_depends_on_locals (h : expr) (hs : List expr) : tactic Bool :=
  hyp_directly_depends_on_local_name_set h <| local_list_to_name_set hs

/-- `hyp_directly_depends_on_local_name_set_inclusive h ns` is true iff the
hypothesis `h` directly depends on a hypothesis whose unique name appears in
`ns` or `h`'s name appears in `ns`.
-/
unsafe def hyp_directly_depends_on_local_name_set_inclusive (h : expr) (ns : name_set) : tactic Bool :=
  List.mbor [pure <| ns.contains h.local_uniq_name, hyp_directly_depends_on_local_name_set h ns]

/-- `hyp_directly_depends_on_local_set_inclusive h ns` is true iff the hypothesis `h`
directly depends on any of the hypotheses `hs` or `h` appears in `hs`.
-/
unsafe def hyp_directly_depends_on_local_set_inclusive (h : expr) (hs : expr_set) : tactic Bool :=
  hyp_directly_depends_on_local_name_set_inclusive h <| local_set_to_name_set hs

/-- `hyp_directly_depends_on_locals_inclusive h ns` is true iff the hypothesis `h`
directly depends on any of the hypotheses `hs` or `h` appears in `hs`.
-/
unsafe def hyp_directly_depends_on_locals_inclusive (h : expr) (hs : List expr) : tactic Bool :=
  hyp_directly_depends_on_local_name_set_inclusive h <| local_list_to_name_set hs

/-! #### Computing the direct dependencies of a hypothesis -/


/-- `direct_dependency_set_of_hyp h` is the set of hypotheses that the hypothesis
`h` directly depends on. These are the hypotheses that appear in `h`'s type or
value (if `h` is a local definition).
-/
unsafe def direct_dependency_set_of_hyp (h : expr) : tactic expr_set := do
  let t ← infer_type h
  let deps := t.list_local_consts'
  let some val ← try_core <| local_def_value h | pure deps
  let deps := deps.union val.list_local_consts'
  pure deps

/-- `direct_dependency_name_set_of_hyp h` is the set of unique names of hypotheses
that the hypothesis `h` directly depends on. These are the hypotheses that
appear in `h`'s type or value (if `h` is a local definition).
-/
unsafe def direct_dependency_name_set_of_hyp (h : expr) : tactic name_set :=
  local_set_to_name_set <$> direct_dependency_set_of_hyp h

/-- `direct_dependencies_of_hyp h` is the list of hypotheses that the hypothesis `h`
directly depends on. These are the hypotheses that appear in `h`'s type or value
(if `h` is a local definition). The dependencies are returned in no particular
order.
-/
unsafe def direct_dependencies_of_hyp (h : expr) : tactic (List expr) :=
  rb_set.to_list <$> direct_dependency_set_of_hyp h

/-- `direct_dependency_set_of_hyp_inclusive h` is the set of hypotheses that the
hypothesis `h` directly depends on, plus `h` itself.
-/
unsafe def direct_dependency_set_of_hyp_inclusive (h : expr) : tactic expr_set := do
  let deps ← direct_dependency_set_of_hyp h
  pure <| deps h

/-- `direct_dependency_name_set_of_hyp_inclusive h` is the set of unique names of
hypotheses that the hypothesis `h` directly depends on, plus `h` itself.
-/
unsafe def direct_dependency_name_set_of_hyp_inclusive (h : expr) : tactic name_set :=
  local_set_to_name_set <$> direct_dependency_set_of_hyp_inclusive h

/-- `direct_dependencies_of_hyp_inclusive h` is the list of hypotheses that the
hypothesis `h` directly depends on, plus `h` itself. The dependencies are
returned in no particular order.
-/
unsafe def direct_dependencies_of_hyp_inclusive (h : expr) : tactic (List expr) :=
  rb_set.to_list <$> direct_dependency_set_of_hyp_inclusive h

/-! ### Indirect/Transitive Dependencies -/


/-! #### Checking whether hypotheses depend on each other -/


/-- `hyp_depends_on_local_name_set' cache h ns` is true iff `h` depends on any of
the hypotheses whose unique names appear in `ns`. `cache` must be a set of
hypotheses known *not* to depend (even indirectly) on any of the `ns`. This is
a performance optimisation, so you can give an empty cache. The tactic also
returns an expanded cache with hypotheses which the tactic has encountered.

You probably want to use `tactic.hyp_depends_on_local_name_set` or
`tactic.hyps_depend_on_local_name_set` instead of this tactic.
-/
unsafe def hyp_depends_on_local_name_set' : expr_set → expr → name_set → tactic (Bool × expr_set) := fun cache h ns =>
  do
  let ff ← pure <| cache.contains h | pure (false, cache)
  let direct_deps ← direct_dependency_set_of_hyp h
  let has_dep := direct_deps.fold false fun d b => b || ns.contains d.local_uniq_name
  let ff ← pure has_dep | pure (true, cache)
  let (has_dep, cache) ←
    (direct_deps.mfold (false, cache)) fun d ⟨b, cache⟩ =>
        if b then pure (true, cache) else hyp_depends_on_local_name_set' cache d ns
  if has_dep then pure (tt, cache) else pure (ff, cache h)

/-- `hyp_depends_on_local_name_set h ns` is true iff the hypothesis `h` depends on
any of the hypotheses whose unique names appear in `ns`. If you need to check
dependencies of multiple hypotheses, use `tactic.hyps_depend_on_local_name_set`.
-/
unsafe def hyp_depends_on_local_name_set (h : expr) (ns : name_set) : tactic Bool := do
  let ctx_has_local_def ← context_upto_hyp_has_local_def h
  if ctx_has_local_def then Prod.fst <$> hyp_depends_on_local_name_set' mk_expr_set h ns
    else hyp_directly_depends_on_local_name_set h ns

/-- `hyp_depends_on_local_set h hs` is true iff the hypothesis `h` depends on
any of the hypotheses `hs`. If you need to check dependencies of multiple
hypotheses, use `tactic.hyps_depend_on_local_set`.
-/
unsafe def hyp_depends_on_local_set (h : expr) (hs : expr_set) : tactic Bool :=
  hyp_depends_on_local_name_set h <| local_set_to_name_set hs

/-- `hyp_depends_on_locals h hs` is true iff the hypothesis `h` depends on any of
the hypotheses `hs`. If you need to check dependencies of multiple hypotheses,
use `tactic.hyps_depend_on_locals`.
-/
unsafe def hyp_depends_on_locals (h : expr) (hs : List expr) : tactic Bool :=
  hyp_depends_on_local_name_set h <| local_list_to_name_set hs

/-- `hyps_depend_on_local_name_set hs ns` returns, for each `h ∈ hs`, whether `h`
depends on a hypothesis whose unique name appears in `ns`. This is the same as
(but more efficient than) calling `tactic.hyp_depends_on_local_name_set` for
every `h ∈ hs`.
-/
unsafe def hyps_depend_on_local_name_set (hs : List expr) (ns : name_set) : tactic (List Bool) := do
  let ctx_has_local ← context_has_local_def
  if ctx_has_local then
      let go : expr → List Bool × expr_set → tactic (List Bool × expr_set) := fun h ⟨deps, cache⟩ => do
        let (h_dep, cache) ← hyp_depends_on_local_name_set' cache h ns
        pure (h_dep :: deps, cache)
      Prod.fst <$> hs go ([], mk_expr_map)
    else hs fun h => hyp_directly_depends_on_local_name_set h ns

/-- `hyps_depend_on_local_set hs is` returns, for each `h ∈ hs`, whether `h` depends
on any of the hypotheses `is`. This is the same as (but more efficient than)
calling `tactic.hyp_depends_on_local_set` for every `h ∈ hs`.
-/
unsafe def hyps_depend_on_local_set (hs : List expr) (is : expr_set) : tactic (List Bool) :=
  hyps_depend_on_local_name_set hs <| local_set_to_name_set is

/-- `hyps_depend_on_locals hs is` returns, for each `h ∈ hs`, whether `h` depends
on any of the hypotheses `is`. This is the same as (but more efficient than)
calling `tactic.hyp_depends_on_locals` for every `h ∈ hs`.
-/
unsafe def hyps_depend_on_locals (hs is : List expr) : tactic (List Bool) :=
  hyps_depend_on_local_name_set hs <| local_list_to_name_set is

/-- `hyp_depends_on_local_name_set_inclusive' cache h ns` is true iff the hypothesis
`h` inclusively depends on a hypothesis whose unique name appears in `ns`.
`cache` must be a set of hypotheses known *not* to depend (even indirectly) on
any of the `ns`. This is a performance optimisation, so you can give an empty
cache. The tactic also returns an expanded cache with hypotheses which the
tactic has encountered. Note that the cache records exclusive, not inclusive
dependencies.

You probably want to use `tactic.hyp_depends_on_local_name_set_inclusive` or
`tactic.hyps_depend_on_local_name_set_inclusive` instead of this tactic.
-/
unsafe def hyp_depends_on_local_name_set_inclusive' (cache : expr_set) (h : expr) (ns : name_set) :
    tactic (Bool × expr_set) :=
  if ns.contains h.local_uniq_name then pure (true, cache) else hyp_depends_on_local_name_set' cache h ns

/-- `hyp_depends_on_local_name_set_inclusive h ns` is true iff the hypothesis `h`
inclusively depends on any of the hypotheses whose unique names appear in `ns`.
If you need to check the dependencies of multiple hypotheses, use
`tactic.hyps_depend_on_local_name_set_inclusive`.
-/
unsafe def hyp_depends_on_local_name_set_inclusive (h : expr) (ns : name_set) : tactic Bool :=
  List.mbor [pure <| ns.contains h.local_uniq_name, hyp_depends_on_local_name_set h ns]

/-- `hyp_depends_on_local_set_inclusive h hs` is true iff the hypothesis `h`
inclusively depends on any of the hypotheses `hs`. If you need to check
dependencies of multiple hypotheses, use
`tactic.hyps_depend_on_local_set_inclusive`.
-/
unsafe def hyp_depends_on_local_set_inclusive (h : expr) (hs : expr_set) : tactic Bool :=
  hyp_depends_on_local_name_set_inclusive h <| local_set_to_name_set hs

/-- `hyp_depends_on_locals_inclusive h hs` is true iff the hypothesis `h`
inclusively depends on any of the hypotheses `hs`. If you need to check
dependencies of multiple hypotheses, use
`tactic.hyps_depend_on_locals_inclusive`.
-/
unsafe def hyp_depends_on_locals_inclusive (h : expr) (hs : List expr) : tactic Bool :=
  hyp_depends_on_local_name_set_inclusive h <| local_list_to_name_set hs

/-- `hyps_depend_on_local_name_set_inclusive hs ns` returns, for each `h ∈ hs`,
whether `h` inclusively depends on a hypothesis whose unique name appears in
`ns`. This is the same as (but more efficient than) calling
`tactic.hyp_depends_on_local_name_set_inclusive` for every `h ∈ hs`.
-/
unsafe def hyps_depend_on_local_name_set_inclusive (hs : List expr) (ns : name_set) : tactic (List Bool) := do
  let ctx_has_local ← context_has_local_def
  if ctx_has_local then
      let go : expr → List Bool × expr_set → tactic (List Bool × expr_set) := fun h ⟨deps, cache⟩ => do
        let (h_dep, cache) ← hyp_depends_on_local_name_set_inclusive' cache h ns
        pure (h_dep :: deps, cache)
      Prod.fst <$> hs go ([], mk_expr_map)
    else hs fun h => hyp_directly_depends_on_local_name_set_inclusive h ns

/-- `hyps_depend_on_local_set_inclusive hs is` returns, for each `h ∈ hs`, whether
`h` depends inclusively on any of the hypotheses `is`. This is the same as
(but more efficient than) calling `tactic.hyp_depends_on_local_set_inclusive`
for every `h ∈ hs`.
-/
unsafe def hyps_depend_on_local_set_inclusive (hs : List expr) (is : expr_set) : tactic (List Bool) :=
  hyps_depend_on_local_name_set_inclusive hs <| local_set_to_name_set is

/-- `hyps_depend_on_locals_inclusive hs is` returns, for each `h ∈ hs`, whether `h`
depends inclusively on any of the hypotheses `is`. This is the same as (but more
efficient than) calling `tactic.hyp_depends_on_locals_inclusive` for every
`h ∈ hs`.
-/
unsafe def hyps_depend_on_locals_inclusive (hs is : List expr) : tactic (List Bool) :=
  hyps_depend_on_local_name_set_inclusive hs <| local_list_to_name_set is

/-! #### Computing the dependencies of a hypothesis -/


/-- `dependency_set_of_hyp' cache h` is the set of dependencies of the hypothesis
`h`. `cache` is a map from hypotheses to all their dependencies (including
indirect dependencies). This is a performance optimisation, so you can give an
empty cache. The tactic also returns an expanded cache with hypotheses which
the tactic has encountered.

You probably want to use `tactic.dependency_set_of_hyp` or
`tactic.dependency_sets_of_hyps` instead of this tactic.
-/
unsafe def dependency_set_of_hyp' : expr_map expr_set → expr → tactic (expr_set × expr_map expr_set) := fun cache h =>
  do
  match cache h with
    | some deps => pure (deps, cache)
    | none => do
      let direct_deps ← direct_dependency_set_of_hyp h
      let (deps, cache) ←
        (direct_deps (direct_deps, cache)) fun h' ⟨deps, cache⟩ => do
            let (deps', cache) ← dependency_set_of_hyp' cache h'
            pure (deps deps', cache)
      pure (deps, cache h deps)

/-- `dependency_set_of_hyp h` is the set of dependencies of the hypothesis `h`. If
you need the dependencies of multiple hypotheses, use
`tactic.dependency_sets_of_hyps`.
-/
unsafe def dependency_set_of_hyp (h : expr) : tactic expr_set := do
  let ctx_has_local ← context_upto_hyp_has_local_def h
  if ctx_has_local then Prod.fst <$> dependency_set_of_hyp' mk_expr_map h else direct_dependency_set_of_hyp h

/-- `dependency_name_set_of_hyp h` is the set of unique names of the dependencies of
the hypothesis `h`. If you need the dependencies of multiple hypotheses, use
`tactic.dependency_name_sets_of_hyps`.
-/
unsafe def dependency_name_set_of_hyp (h : expr) : tactic name_set :=
  local_set_to_name_set <$> dependency_set_of_hyp h

/-- `dependencies_of_hyp h` is the list of dependencies of the hypothesis `h`.
The dependencies are returned in no particular order. If you need the
dependencies of multiple hypotheses, use `tactic.dependencies_of_hyps`.
-/
unsafe def dependencies_of_hyp (h : expr) : tactic (List expr) :=
  rb_set.to_list <$> dependency_set_of_hyp h

/-- `dependency_sets_of_hyps hs` returns, for each `h ∈ hs`, the set of dependencies
of `h`. This is the same as (but more performant than) using
`tactic.dependency_set_of_hyp` on every `h ∈ hs`.
-/
unsafe def dependency_sets_of_hyps (hs : List expr) : tactic (List expr_set) := do
  let ctx_has_def ← context_has_local_def
  if ctx_has_def then
      let go : expr → List expr_set × expr_map expr_set → tactic (List expr_set × expr_map expr_set) := do
        fun h ⟨deps, cache⟩ => do
          let (h_deps, cache) ← dependency_set_of_hyp' cache h
          pure (h_deps :: deps, cache)
      Prod.fst <$> hs go ([], mk_expr_map)
    else hs direct_dependency_set_of_hyp

/-- `dependency_name_sets_of_hyps hs` returns, for each `h ∈ hs`, the set of unique
names of the dependencies of `h`. This is the same as (but more performant than)
using `tactic.dependency_name_set_of_hyp` on every `h ∈ hs`.
-/
unsafe def dependency_name_sets_of_hyps (hs : List expr) : tactic (List name_set) :=
  List.map local_set_to_name_set <$> dependency_sets_of_hyps hs

/-- `dependencies_of_hyps hs` returns, for each `h ∈ hs`, the dependencies of `h`.
The dependencies appear in no particular order in the returned lists. This is
the same as (but more performant than) using `tactic.dependencies_of_hyp` on
every `h ∈ hs`.
-/
unsafe def dependencies_of_hyps (hs : List expr) : tactic (List (List expr)) :=
  List.map rb_set.to_list <$> dependency_sets_of_hyps hs

/-- `dependency_set_of_hyp_inclusive' cache h` is the set of dependencies of the
hypothesis `h`, plus `h` itself. `cache` is a map from hypotheses to all their
dependencies (including indirect dependencies). This is a performance
optimisation, so you can give an empty cache. The tactic also returns an
expanded cache with hypotheses which the tactic has encountered. Note that the
cache records exclusive, not inclusive dependencies.

You probably want to use `tactic.dependency_set_of_hyp_inclusive` or
`tactic.dependency_sets_of_hyps_inclusive` instead of this tactic.
-/
unsafe def dependency_set_of_hyp_inclusive' (cache : expr_map expr_set) (h : expr) :
    tactic (expr_set × expr_map expr_set) := do
  let (deps, cache) ← dependency_set_of_hyp' cache h
  pure (deps h, cache)

/-- `dependency_set_of_hyp_inclusive h` is the set of dependencies of the hypothesis
`h`, plus `h` itself. If you need the dependencies of multiple hypotheses, use
`tactic.dependency_sets_of_hyps_inclusive`.
-/
unsafe def dependency_set_of_hyp_inclusive (h : expr) : tactic expr_set := do
  let deps ← dependency_set_of_hyp h
  pure <| deps h

/-- `dependency_name_set_of_hyp_inclusive h` is the set of unique names of the
dependencies of the hypothesis `h`, plus the unique name of `h` itself. If you
need the dependencies of multiple hypotheses, use
`tactic.dependency_name_sets_of_hyps_inclusive`.
-/
unsafe def dependency_name_set_of_hyp_inclusive (h : expr) : tactic name_set :=
  local_set_to_name_set <$> dependency_set_of_hyp_inclusive h

/-- `dependencies_of_hyp_inclusive h` is the list of dependencies of the hypothesis
`h`, plus `h` itself. The dependencies are returned in no particular order. If
you need the dependencies of multiple hypotheses, use
`tactic.dependencies_of_hyps_inclusive`.
-/
unsafe def dependencies_of_hyp_inclusive (h : expr) : tactic (List expr) :=
  rb_set.to_list <$> dependency_set_of_hyp_inclusive h

/-- `dependency_sets_of_hyps_inclusive hs` returns, for each `h ∈ hs`, the
dependencies of `h`, plus `h` itself. This is the same as (but more performant
than) using `tactic.dependency_set_of_hyp_inclusive` on every `h ∈ hs`.
-/
unsafe def dependency_sets_of_hyps_inclusive (hs : List expr) : tactic (List expr_set) := do
  let ctx_has_def ← context_has_local_def
  if ctx_has_def then
      let go : expr → List expr_set × expr_map expr_set → tactic (List expr_set × expr_map expr_set) :=
        fun h ⟨deps, cache⟩ => do
        let (h_deps, cache) ← dependency_set_of_hyp_inclusive' cache h
        pure (h_deps :: deps, cache)
      Prod.fst <$> hs go ([], mk_expr_map)
    else hs direct_dependency_set_of_hyp_inclusive

/-- `dependency_name_sets_of_hyps_inclusive hs` returns, for each `h ∈ hs`, the
unique names of the dependencies of `h`, plus the unique name of `h` itself.
This is the same as (but more performant than) using
`tactic.dependency_name_set_of_hyp_inclusive` on every `h ∈ hs`.
-/
unsafe def dependency_name_sets_of_hyps_inclusive (hs : List expr) : tactic (List name_set) :=
  List.map local_set_to_name_set <$> dependency_sets_of_hyps_inclusive hs

/-- `dependencies_of_hyps_inclusive hs` returns, for each `h ∈ hs`, the dependencies
of `h`, plus `h` itself. The dependencies appear in no particular order in the
returned lists. This is the same as (but more performant than) using
`tactic.dependencies_of_hyp_inclusive` on every `h ∈ hs`.
-/
unsafe def dependencies_of_hyps_inclusive (hs : List expr) : tactic (List (List expr)) :=
  List.map rb_set.to_list <$> dependency_sets_of_hyps_inclusive hs

/-! #### Computing the reverse dependencies of a hypothesis -/


private unsafe def reverse_dependencies_of_hyp_name_set_aux (hs : name_set) :
    List expr → List expr → name_set → tactic (List expr)
  | [], revdeps, _ => pure revdeps.reverse
  | H :: Hs, revdeps, ns => do
    let H_uname := H.local_uniq_name
    let H_is_revdep ← List.mband [pure <| ¬hs.contains H_uname, hyp_directly_depends_on_local_name_set H ns]
    if H_is_revdep then reverse_dependencies_of_hyp_name_set_aux Hs (H :: revdeps) (ns H_uname)
      else reverse_dependencies_of_hyp_name_set_aux Hs revdeps ns

/-- `reverse_dependencies_of_hyp_name_set hs` is the list of reverse dependencies of
the hypotheses whose unique names appear in `hs`, excluding the `hs` themselves.
The reverse dependencies are returned in the order in which they appear in the
context.
-/
unsafe def reverse_dependencies_of_hyp_name_set (hs : name_set) : tactic (List expr) := do
  let ctx ← local_context
  let ctx := ctx.after fun h => hs.contains h.local_uniq_name
  reverse_dependencies_of_hyp_name_set_aux hs ctx [] hs

/-- `reverse_dependencies_of_hyp_set hs` is the list of reverse dependencies of the
hypotheses `hs`, excluding the `hs` themselves. The reverse dependencies are
returned in the order in which they appear in the context.
-/
unsafe def reverse_dependencies_of_hyp_set (hs : expr_set) : tactic (List expr) :=
  reverse_dependencies_of_hyp_name_set <| local_set_to_name_set hs

/-- `reverse_dependencies_of_hyps hs` is the list of reverse dependencies of the
hypotheses `hs`, excluding the `hs` themselves. The reverse dependencies are
returned in the order in which they appear in the context.
-/
unsafe def reverse_dependencies_of_hyps (hs : List expr) : tactic (List expr) :=
  reverse_dependencies_of_hyp_name_set <| local_list_to_name_set hs

private unsafe def reverse_dependencies_of_hyp_name_set_inclusive_aux :
    List expr → List expr → name_set → tactic (List expr)
  | [], revdeps, _ => pure revdeps.reverse
  | H :: Hs, revdeps, ns => do
    let H_uname := H.local_uniq_name
    let H_is_revdep ← List.mbor [pure <| ns.contains H.local_uniq_name, hyp_directly_depends_on_local_name_set H ns]
    if H_is_revdep then reverse_dependencies_of_hyp_name_set_inclusive_aux Hs (H :: revdeps) (ns H_uname)
      else reverse_dependencies_of_hyp_name_set_inclusive_aux Hs revdeps ns

/-- `reverse_dependencies_of_hyp_name_set_inclusive hs` is the list of reverse
dependencies of the hypotheses whose unique names appear in `hs`, including the
`hs` themselves. The reverse dependencies are returned in the order in which
they appear in the context.
-/
unsafe def reverse_dependencies_of_hyp_name_set_inclusive (hs : name_set) : tactic (List expr) := do
  let ctx ← local_context
  let ctx := ctx.dropWhile fun h => ¬hs.contains h.local_uniq_name
  reverse_dependencies_of_hyp_name_set_inclusive_aux ctx [] hs

/-- `reverse_dependencies_of_hyp_set_inclusive hs` is the list of reverse
dependencies of the hypotheses `hs`, including the `hs` themselves. The
inclusive reverse dependencies are returned in the order in which they appear in
the context.
-/
unsafe def reverse_dependencies_of_hyp_set_inclusive (hs : expr_set) : tactic (List expr) :=
  reverse_dependencies_of_hyp_name_set_inclusive <| local_set_to_name_set hs

/-- `reverse_dependencies_of_hyps_inclusive hs` is the list of reverse dependencies
of the hypotheses `hs`, including the `hs` themselves. The reverse dependencies
are returned in the order in which they appear in the context.
-/
unsafe def reverse_dependencies_of_hyps_inclusive (hs : List expr) : tactic (List expr) :=
  reverse_dependencies_of_hyp_name_set_inclusive <| local_list_to_name_set hs

/-! ### Reverting a hypothesis and its reverse dependencies -/


/-- `revert_name_set hs` reverts the hypotheses whose unique names appear in `hs`,
as well as any hypotheses that depend on them. Returns the number of reverted
hypotheses and a list containing these hypotheses. The reverted hypotheses are
returned in the order in which they used to appear in the context and are
guaranteed to store the correct type (see `tactic.update_type`).
-/
unsafe def revert_name_set (hs : name_set) : tactic (ℕ × List expr) := do
  let to_revert ← reverse_dependencies_of_hyp_name_set_inclusive hs
  let to_revert_with_types ← to_revert.mmap update_type
  let num_reverted ← revert_lst to_revert
  pure (num_reverted, to_revert_with_types)

/-- `revert_set hs` reverts the hypotheses `hs`, as well as any hypotheses that
depend on them. Returns the number of reverted hypotheses and a list containing
these hypotheses. The reverted hypotheses are returned in the order in which
they used to appear in the context and are guaranteed to store the correct type
(see `tactic.update_type`).
-/
unsafe def revert_set (hs : expr_set) : tactic (ℕ × List expr) :=
  revert_name_set <| local_set_to_name_set hs

/-- `revert_lst' hs` reverts the hypotheses `hs`, as well as any hypotheses that
depend on them. Returns the number of reverted hypotheses and a list containing
these hypotheses. The reverted hypotheses are returned in the order in which
they used to appear in the context and are guaranteed to store the correct type
(see `tactic.update_type`).

This is a more informative version of `tactic.revert_lst`.
-/
unsafe def revert_lst' (hs : List expr) : tactic (ℕ × List expr) :=
  revert_name_set <| local_list_to_name_set hs

/-- `revert_reverse_dependencies_of_hyp h` reverts all the hypotheses that depend on
the hypothesis `h`, including the local definitions that have `h` in their
value. This fixes a bug in `tactic.revert_kdependencies` that does not revert
local definitions for which `h` only appears in the value. Returns the number
of reverted hypotheses.
-/
/- We cannot implement it as `revert e >> intro1` because that would change the
local constant in the context. -/
unsafe def revert_reverse_dependencies_of_hyp (h : expr) : tactic ℕ :=
  reverse_dependencies_of_hyp_name_set (mk_name_set.insert h.local_uniq_name) >>= revert_lst

/-- `revert_reverse_dependencies_of_hyp_name_set hs` reverts all the hypotheses that
depend on a hypothesis whose unique name appears in `hs`. The `hs` themselves
are not reverted, unless they depend on each other. Returns the number of
reverted hypotheses.
-/
unsafe def revert_reverse_dependencies_of_hyp_name_set (hs : name_set) : tactic ℕ :=
  reverse_dependencies_of_hyp_name_set hs >>= revert_lst

/-- `revert_reverse_dependencies_of_hyp_set hs` reverts all the hypotheses that
depend on a hypothesis in `hs`. The `hs` themselves are not reverted, unless
they depend on each other. Returns the number of reverted hypotheses.
-/
unsafe def revert_reverse_dependencies_of_hyp_set (hs : expr_set) : tactic ℕ :=
  reverse_dependencies_of_hyp_set hs >>= revert_lst

/-- `revert_reverse_dependencies_of_hyp hs` reverts all the hypotheses that depend
on a hypothesis in `hs`. The `hs` themselves are not reverted, unless they
depend on each other. Returns the number of reverted hypotheses.
-/
unsafe def revert_reverse_dependencies_of_hyps (hs : List expr) : tactic ℕ :=
  reverse_dependencies_of_hyps hs >>= revert_lst

end Tactic

