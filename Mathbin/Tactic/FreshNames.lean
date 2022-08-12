/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Mathbin.Data.Sum.Basic
import Mathbin.Tactic.Dependencies

/-!
# Tactics for giving hypotheses fresh names

When introducing hypotheses, we often want to make sure that their names are
fresh, i.e. not used by any other hypothesis in the context. This file provides
tactics which allow you to give a list of possible names for each hypothesis,
with the tactics picking the first name that is not yet used in the context. If
all names are already used, the tactics use a name derived from the first name
in the list.
-/


namespace Tactic

-- This implementation is a bit of a hack, but probably fine in practice since
-- we're unlikely to need more than two or three iterations of the loop.
private unsafe def get_unused_name_reserved_aux (n : Name) (reserved : name_set) : Option Nat → tactic Name :=
  fun suffix => do
  let n ← get_unused_name n suffix
  if ¬reserved n then pure n
    else do
      let new_suffix :=
        match suffix with
        | none => some 1
        | some n => some (n + 1)
      get_unused_name_reserved_aux new_suffix

/-- `get_unused_name_reserved ns reserved` returns the first name from `ns` that
occurs neither in `reserved` nor in the environment. If there is no such name in
`ns`, it returns a name of the form `n_i`, where `n` is the first name from `ns`
and `i` is a natural number (like `tactic.get_unused_name`). If `ns` is empty,
it returns an arbitrary name.

For example, assume we operate in the following context:

```
n n_1: ℕ
```

Then we have

```
get_unused_name_reserved [`n, `m, `list, `o] {m} = `o
```

since `n occurs in the context, `m is reserved, `list occurs in the environment
but `o is unused. We also have

```
get_unused_name_reserved [`n, `m, `list] {m} = `n_2
```

since all of the names from the list are taken and `n_2` is the first unused
variation of `n`.
-/
unsafe def get_unused_name_reserved (ns : List Name) (reserved : name_set) : tactic Name :=
  (first <|
      ns.map fun n => do
        guardₓ ¬reserved n
        fail_if_success (resolve_name n)
        pure n) <|>
    do
    let fallback :=
      match ns with
      | [] => `x
      | x :: _ => x
    get_unused_name_reserved_aux fallback reserved none

/-- `intro_fresh_reserved ns reserved` introduces a hypothesis. The hypothesis
receives a fresh name from `ns`, excluding the names in `reserved`. `ns` must be
nonempty. See `tactic.get_unused_name_reserved` for the full algorithm.
-/
unsafe def intro_fresh_reserved (ns : List Name) (reserved : name_set) : tactic expr :=
  get_unused_name_reserved ns reserved >>= intro

/-- `intro_lst_fresh_reserved ns reserved` introduces one hypothesis for every
element of `ns`. If the element is `sum.inl n`, the hypothesis receives the name
`n` (which may or may not be fresh). If the element is `sum.inr ns'`, the
hypothesis receives a fresh name from `ns`, excluding the names in `reserved`.
`ns` must be nonempty. See `tactic.get_unused_name_reserved` for the full
algorithm.

Note that the
order of introductions matters:
`intro_lst_fresh_reserved [sum.inr [`n], sum.inr [`n]]` will introduce
hypotheses `n` and `n_1` (assuming that these names are otherwise unused and not
reserved).
-/
unsafe def intro_lst_fresh_reserved (ns : List (Sum Name (List Name))) (reserved : name_set) : tactic (List expr) :=
  ns.mmap fun spec =>
    match spec with
    | Sum.inl n => intro n
    | Sum.inr ns => intro_fresh_reserved ns reserved

/-- `rename_fresh renames reserved`, given a map `renames` which associates the
unique names of some hypotheses `hᵢ` with either a name `nᵢ` or a nonempty (!)
name list `nsᵢ`, renames each `hᵢ` as follows:

- If `hᵢ` is associated with a name `nᵢ`, it is renamed to `nᵢ`. This may
  introduce shadowing if there is another hypothesis `nᵢ` in the context.
- If `hᵢ` is associated with a name list `nsᵢ`, it is renamed to the first
  unused name from `nsᵢ`. If none of the names is unused, `hᵢ` is renamed to a
  fresh name based on the first name of `nᵢ`. A name is considered used if it
  appears in the context or in the environment or in `reserved`.

See `tactic.get_unused_name_reserved` for the full algorithm.

The hypotheses are renamed in context order, so hypotheses which occur earlier
in the context are renamed before hypotheses that occur later in the context.
This is important because earlier renamings may 'steal' names from later
renamings.

`rename_fresh` returns a list of pairs `(oᵢ, nᵢ)` where the `oᵢ` are hypotheses
from the context in which `rename_fresh` was called and the `nᵢ` are the
corresponding hypotheses from the new context created by `rename_fresh`. The
pairs are returned in context order. Note that the returned list may contain
hypotheses which do not appear in `renames` but had to be temporarily reverted
due to dependencies.
-/
unsafe def rename_fresh (renames : name_map (Sum Name (List Name))) (reserved : name_set) :
    tactic (List (expr × expr)) := do
  let (_, reverted) ← revert_name_set <| name_set.of_list <| renames.keys
  let renames :=
    reverted.map fun h =>
      match renames.find h.local_uniq_name with
      | none => Sum.inl h.local_pp_name
      | some new_names => new_names
  let reserved := reserved.insert_list <| renames.filterMap Sum.getLeft
  let new_hyps ← intro_lst_fresh_reserved renames reserved
  pure <| reverted new_hyps

end Tactic

