/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Tactic.DocCommands

open Lean.Parser Tactic Interactive

/-- `restate_axiom` takes a structure field, and makes a new, definitionally simplified copy of it.
If the existing field name ends with a `'`, the new field just has the prime removed. Otherwise,
we append `_lemma`.
The main application is to provide clean versions of structure fields that have been tagged with
an auto_param.
-/
unsafe def restate_axiom (d : declaration) (new_name : Name) : tactic Unit := do
  let (levels, type, value, reducibility, trusted) ←
    pure
        (match d.to_definition with
        | declaration.defn Name levels type value reducibility trusted => (levels, type, value, reducibility, trusted)
        | _ => undefined)
  let (s, u) ← mk_simp_set false [] []
  let new_type ← s.dsimplify [] type <|> pure type
  let prop ← is_prop new_type
  let new_decl :=
    if prop then declaration.thm new_name levels new_type (task.pure value)
    else declaration.defn new_name levels new_type value reducibility trusted
  updateex_env fun env => env new_decl

private unsafe def name_lemma (old : Name) (new : Option Name := none) : tactic Name :=
  match new with
  | none =>
    match old.components.reverse with
    | last :: most =>
      (do
          let last := last.toString
          let last :=
            if last.toList.ilast = ''' then (last.toList.reverse.drop 1).reverse.asString else last ++ "_lemma"
          return (mkStrName old last)) <|>
        failed
    | nil => undefined
  | some new => return (mkStrName old.getPrefix new.toString)

/-- `restate_axiom` makes a new copy of a structure field, first definitionally simplifying the type.
This is useful to remove `auto_param` or `opt_param` from the statement.

As an example, we have:
```lean
structure A :=
(x : ℕ)
(a' : x = 1 . skip)

example (z : A) : z.x = 1 := by rw A.a' -- rewrite tactic failed, lemma is not an equality nor a iff

restate_axiom A.a'
example (z : A) : z.x = 1 := by rw A.a
```

By default, `restate_axiom` names the new lemma by removing a trailing `'`, or otherwise appending
`_lemma` if there is no trailing `'`. You can also give `restate_axiom` a second argument to
specify the new name, as in
```lean
restate_axiom A.a f
example (z : A) : z.x = 1 := by rw A.f
```
-/
@[user_command]
unsafe def restate_axiom_cmd (_ : parse <| tk "restate_axiom") : lean.parser Unit := do
  let from_lemma ← ident
  let new_name ← optionalₓ ident
  let from_lemma_fully_qualified ← resolve_constant from_lemma
  let d ← get_decl from_lemma_fully_qualified <|> fail ("declaration " ++ toString from_lemma ++ " not found")
  do
    let new_name ← name_lemma from_lemma_fully_qualified new_name
    restate_axiom d new_name

add_tactic_doc
  { Name := "restate_axiom", category := DocCategory.cmd, declNames := [`restate_axiom_cmd],
    tags := ["renaming", "environment"] }

