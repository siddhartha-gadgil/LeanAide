/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathbin.Tactic.FixReflectString

/-!
# Documentation commands

We generate html documentation from mathlib. It is convenient to collect lists of tactics, commands,
notes, etc. To facilitate this, we declare these documentation entries in the library
using special commands.

* `library_note` adds a note describing a certain feature or design decision. These can be
  referenced in doc strings with the text `note [name of note]`.
* `add_tactic_doc` adds an entry documenting an interactive tactic, command, hole command, or
  attribute.

Since these commands are used in files imported by `tactic.core`, this file has no imports.

## Implementation details

`library_note note_id note_msg` creates a declaration `` `library_note.i `` for some `i`.
This declaration is a pair of strings `note_id` and `note_msg`, and it gets tagged with the
`library_note` attribute.

Similarly, `add_tactic_doc` creates a declaration `` `tactic_doc.i `` that stores the provided
information.
-/


/-- A rudimentary hash function on strings. -/
def Stringₓ.hash (s : Stringₓ) : ℕ :=
  s.fold 1 fun h c => (33 * h + c.val) % unsignedSz

/-- `mk_hashed_name nspace id` hashes the string `id` to a value `i` and returns the name
`nspace._i` -/
unsafe def string.mk_hashed_name (nspace : Name) (id : Stringₓ) : Name :=
  mkStrName nspace ("_" ++ toString id.hash)

open Tactic

/-- `copy_doc_string fr to` copies the docstring from the declaration named `fr`
to each declaration named in the list `to`. -/
unsafe def tactic.copy_doc_string (fr : Name) (to : List Name) : tactic Unit := do
  let fr_ds ← doc_string fr
  to fun tgt => add_doc_string tgt fr_ds

open Lean Lean.Parser Interactive

/-- `copy_doc_string source → target_1 target_2 ... target_n` copies the doc string of the
declaration named `source` to each of `target_1`, `target_2`, ..., `target_n`.
 -/
@[user_command]
unsafe def copy_doc_string_cmd (_ : parse (tk "copy_doc_string")) : parser Unit := do
  let fr ← parser.ident
  tk "->"
  let to ← parser.many parser.ident
  let expr.const fr _ ← resolve_name fr
  let to ← parser.of_tactic (to.mmap fun n => expr.const_name <$> resolve_name n)
  tactic.copy_doc_string fr to

/-! ### The `library_note` command -/


/-- A user attribute `library_note` for tagging decls of type `string × string` for use in note
output. -/
@[user_attribute]
unsafe def library_note_attr : user_attribute where
  Name := `library_note
  descr := "Notes about library features to be included in documentation"
  parser := failed

/-- `mk_reflected_definition name val` constructs a definition declaration by reflection.

Example: ``mk_reflected_definition `foo 17`` constructs the definition
declaration corresponding to `def foo : ℕ := 17`
-/
unsafe def mk_reflected_definition (decl_name : Name) {type} [reflected _ type] (body : type) [reflected _ body] :
    declaration :=
  mk_definition decl_name (reflect type).collect_univ_params (reflect type) (reflect body)

/-- If `note_name` and `note` are `pexpr`s representing strings,
`add_library_note note_name note` adds a declaration of type `string × string` and tags it with
the `library_note` attribute. -/
unsafe def tactic.add_library_note (note_name note : Stringₓ) : tactic Unit := do
  let decl_name := note_name.mk_hashed_name `library_note
  add_decl <| mk_reflected_definition decl_name (note_name, note)
  library_note_attr decl_name () tt none

open Tactic

/-- A command to add library notes. Syntax:
```
/--
note message
-/
library_note "note id"
```
-/
@[user_command]
unsafe def library_note (mi : interactive.decl_meta_info) (_ : parse (tk "library_note")) : parser Unit := do
  let note_name ← parser.pexpr
  let note_name ← eval_pexpr Stringₓ note_name
  let some doc_string ← pure mi.doc_string | fail "library_note requires a doc string"
  add_library_note note_name doc_string

/-- Collects all notes in the current environment.
Returns a list of pairs `(note_id, note_content)` -/
unsafe def tactic.get_library_notes : tactic (List (Stringₓ × Stringₓ)) :=
  attribute.get_instances `library_note >>= List.mmapₓ fun dcl => mk_const dcl >>= eval_expr (Stringₓ × Stringₓ)

/-! ### The `add_tactic_doc_entry` command -/


/-- The categories of tactic doc entry. -/
inductive DocCategory
  | tactic
  | cmd
  | hole_cmd
  | attr
  deriving DecidableEq, has_reflect

/-- Format a `doc_category` -/
unsafe def doc_category.to_string : DocCategory → Stringₓ
  | DocCategory.tactic => "tactic"
  | DocCategory.cmd => "command"
  | DocCategory.hole_cmd => "hole_command"
  | DocCategory.attr => "attribute"

unsafe instance : has_to_format DocCategory :=
  ⟨↑doc_category.to_string⟩

/-- The information used to generate a tactic doc entry -/
structure TacticDocEntry where
  Name : Stringₓ
  category : DocCategory
  declNames : List Name
  tags : List Stringₓ := []
  description : Stringₓ := ""
  inheritDescriptionFrom : Option Name := none
  deriving has_reflect

/-- Turns a `tactic_doc_entry` into a JSON representation. -/
unsafe def tactic_doc_entry.to_json (d : TacticDocEntry) : json :=
  json.object
    [("name", d.Name), ("category", d.category.toString), ("decl_names", d.declNames.map (json.of_string ∘ toString)),
      ("tags", d.tags.map json.of_string), ("description", d.description)]

unsafe instance : HasToString TacticDocEntry :=
  ⟨json.unparse ∘ tactic_doc_entry.to_json⟩

/-- `update_description_from tde inh_id` replaces the `description` field of `tde` with the
    doc string of the declaration named `inh_id`. -/
unsafe def tactic_doc_entry.update_description_from (tde : TacticDocEntry) (inh_id : Name) : tactic TacticDocEntry := do
  let ds ← doc_string inh_id <|> fail (toString inh_id ++ " has no doc string")
  return { tde with description := ds }

/-- `update_description tde` replaces the `description` field of `tde` with:

* the doc string of `tde.inherit_description_from`, if this field has a value
* the doc string of the entry in `tde.decl_names`, if this field has length 1

If neither of these conditions are met, it returns `tde`. -/
unsafe def tactic_doc_entry.update_description (tde : TacticDocEntry) : tactic TacticDocEntry :=
  match tde.inheritDescriptionFrom, tde.declNames with
  | some inh_id, _ => tde.update_description_from inh_id
  | none, [inh_id] => tde.update_description_from inh_id
  | none, _ => return tde

/-- A user attribute `tactic_doc` for tagging decls of type `tactic_doc_entry`
for use in doc output -/
@[user_attribute]
unsafe def tactic_doc_entry_attr : user_attribute where
  Name := `tactic_doc
  descr := "Information about a tactic to be included in documentation"
  parser := failed

/-- Collects everything in the environment tagged with the attribute `tactic_doc`. -/
unsafe def tactic.get_tactic_doc_entries : tactic (List TacticDocEntry) :=
  attribute.get_instances `tactic_doc >>= List.mmapₓ fun dcl => mk_const dcl >>= eval_expr TacticDocEntry

/-- `add_tactic_doc tde` adds a declaration to the environment
with `tde` as its body and tags it with the `tactic_doc`
attribute. If `tde.decl_names` has exactly one entry `` `decl`` and
if `tde.description` is the empty string, `add_tactic_doc` uses the doc
string of `decl` as the description. -/
unsafe def tactic.add_tactic_doc (tde : TacticDocEntry) : tactic Unit := do
  when (tde = "" ∧ tde ∧ tde ≠ 1) <|
      fail
        "A tactic doc entry must either:\n 1. have a description written as a doc-string for the `add_tactic_doc` invocation, or\n 2. have a single declaration in the `decl_names` field, to inherit a description from, or\n 3. explicitly indicate the declaration to inherit the description from using\n    `inherit_description_from`."
  let tde ← if tde.description = "" then tde.update_description else return tde
  let decl_name := (tde.Name ++ tde.category.toString).mk_hashed_name `tactic_doc
  add_decl <| mk_definition decl_name [] (quote.1 TacticDocEntry) (reflect tde)
  tactic_doc_entry_attr decl_name () tt none

/-- A command used to add documentation for a tactic, command, hole command, or attribute.

Usage: after defining an interactive tactic, command, or attribute,
add its documentation as follows.
```lean
/--
describe what the command does here
-/
add_tactic_doc
{ name := "display name of the tactic",
  category := cat,
  decl_names := [`dcl_1, `dcl_2],
  tags := ["tag_1", "tag_2"] }
```

The argument to `add_tactic_doc` is a structure of type `tactic_doc_entry`.
* `name` refers to the display name of the tactic; it is used as the header of the doc entry.
* `cat` refers to the category of doc entry.
  Options: `doc_category.tactic`, `doc_category.cmd`, `doc_category.hole_cmd`, `doc_category.attr`
* `decl_names` is a list of the declarations associated with this doc. For instance,
  the entry for `linarith` would set ``decl_names := [`tactic.interactive.linarith]``.
  Some entries may cover multiple declarations.
  It is only necessary to list the interactive versions of tactics.
* `tags` is an optional list of strings used to categorize entries.
* The doc string is the body of the entry. It can be formatted with markdown.
  What you are reading now is the description of `add_tactic_doc`.

If only one related declaration is listed in `decl_names` and if this
invocation of `add_tactic_doc` does not have a doc string, the doc string of
that declaration will become the body of the tactic doc entry. If there are
multiple declarations, you can select the one to be used by passing a name to
the `inherit_description_from` field.

If you prefer a tactic to have a doc string that is different then the doc entry,
you should write the doc entry as a doc string for the `add_tactic_doc` invocation.

Note that providing a badly formed `tactic_doc_entry` to the command can result in strange error
messages.

-/
@[user_command]
unsafe def add_tactic_doc_command (mi : interactive.decl_meta_info) (_ : parse <| tk "add_tactic_doc") : parser Unit :=
  do
  let pe ← parser.pexpr
  let e ← eval_pexpr TacticDocEntry pe
  let e : TacticDocEntry :=
    match mi.doc_string with
    | some desc => { e with description := desc }
    | none => e
  tactic.add_tactic_doc e

/-- At various places in mathlib, we leave implementation notes that are referenced from many other
files. To keep track of these notes, we use the command `library_note`. This makes it easy to
retrieve a list of all notes, e.g. for documentation output.

These notes can be referenced in mathlib with the syntax `Note [note id]`.
Often, these references will be made in code comments (`--`) that won't be displayed in docs.
If such a reference is made in a doc string or module doc, it will be linked to the corresponding
note in the doc display.

Syntax:
```
/--
note message
-/
library_note "note id"
```

An example from `meta.expr`:

```
/--
Some declarations work with open expressions, i.e. an expr that has free variables.
Terms will free variables are not well-typed, and one should not use them in tactics like
`infer_type` or `unify`. You can still do syntactic analysis/manipulation on them.
The reason for working with open types is for performance: instantiating variables requires
iterating through the expression. In one performance test `pi_binders` was more than 6x
quicker than `mk_local_pis` (when applied to the type of all imported declarations 100x).
-/
library_note "open expressions"
```

This note can be referenced near a usage of `pi_binders`:


```
-- See Note [open expressions]
/-- behavior of f -/
def f := pi_binders ...
```
-/
add_tactic_doc
  { Name := "library_note", category := DocCategory.cmd, declNames := [`library_note, `tactic.add_library_note],
    tags := ["documentation"], inheritDescriptionFrom := `library_note }

add_tactic_doc
  { Name := "add_tactic_doc", category := DocCategory.cmd,
    declNames := [`add_tactic_doc_command, `tactic.add_tactic_doc], tags := ["documentation"],
    inheritDescriptionFrom := `add_tactic_doc_command }

add_tactic_doc
  { Name := "copy_doc_string", category := DocCategory.cmd,
    declNames := [`copy_doc_string_cmd, `tactic.copy_doc_string], tags := ["documentation"],
    inheritDescriptionFrom := `copy_doc_string_cmd }

/-- The congruence closure tactic `cc` tries to solve the goal by chaining
equalities from context and applying congruence (i.e. if `a = b`, then `f a = f b`).
It is a finishing tactic, i.e. it is meant to close
the current goal, not to make some inconclusive progress.
A mostly trivial example would be:

```lean
example (a b c : ℕ) (f : ℕ → ℕ) (h: a = b) (h' : b = c) : f a = f c := by cc
```

As an example requiring some thinking to do by hand, consider:

```lean
example (f : ℕ → ℕ) (x : ℕ)
  (H1 : f (f (f x)) = x) (H2 : f (f (f (f (f x)))) = x) :
  f x = x :=
by cc
```

The tactic works by building an equality matching graph. It's a graph where
the vertices are terms and they are linked by edges if they are known to
be equal. Once you've added all the equalities in your context, you take
the transitive closure of the graph and, for each connected component
(i.e. equivalence class) you can elect a term that will represent the
whole class and store proofs that the other elements are equal to it.
You then take the transitive closure of these equalities under the
congruence lemmas.

The `cc` implementation in Lean does a few more tricks: for example it
derives `a=b` from `nat.succ a = nat.succ b`, and `nat.succ a !=
nat.zero` for any `a`.

* The starting reference point is Nelson, Oppen, [Fast decision procedures based on congruence
closure](http://www.cs.colorado.edu/~bec/courses/csci5535-s09/reading/nelson-oppen-congruence.pdf),
Journal of the ACM (1980)

* The congruence lemmas for dependent type theory as used in Lean are described in
[Congruence closure in intensional type theory](https://leanprover.github.io/papers/congr.pdf)
(de Moura, Selsam IJCAR 2016).
-/
-- add docs to core tactics
add_tactic_doc
  { Name := "cc (congruence closure)", category := DocCategory.tactic, declNames := [`tactic.interactive.cc],
    tags := ["core", "finishing"] }

/-- `conv {...}` allows the user to perform targeted rewriting on a goal or hypothesis,
by focusing on particular subexpressions.

See <https://leanprover-community.github.io/extras/conv.html> for more details.

Inside `conv` blocks, mathlib currently additionally provides
* `erw`,
* `ring`, `ring2` and `ring_exp`,
* `norm_num`,
* `norm_cast`,
* `apply_congr`, and
* `conv` (within another `conv`).

`apply_congr` applies congruence lemmas to step further inside expressions,
and sometimes gives better results than the automatically generated
congruence lemmas used by `congr`.

Using `conv` inside a `conv` block allows the user to return to the previous
state of the outer `conv` block after it is finished. Thus you can continue
editing an expression without having to start a new `conv` block and re-scoping
everything. For example:
```lean
example (a b c d : ℕ) (h₁ : b = c) (h₂ : a + c = a + d) : a + b = a + d :=
by conv
{ to_lhs,
  conv
  { congr, skip,
    rw h₁ },
  rw h₂, }
```
Without `conv`, the above example would need to be proved using two successive
`conv` blocks, each beginning with `to_lhs`.

Also, as a shorthand, `conv_lhs` and `conv_rhs` are provided, so that
```lean
example : 0 + 0 = 0 :=
begin
  conv_lhs { simp }
end
```
just means
```lean
example : 0 + 0 = 0 :=
begin
  conv { to_lhs, simp }
end
```
and likewise for `to_rhs`.
-/
add_tactic_doc
  { Name := "conv", category := DocCategory.tactic, declNames := [`tactic.interactive.conv], tags := ["core"] }

add_tactic_doc
  { Name := "simp", category := DocCategory.tactic, declNames := [`tactic.interactive.simp],
    tags := ["core", "simplification"] }

/-- Accepts terms with the type `component tactic_state string` or `html empty` and
renders them interactively.
Requires a compatible version of the vscode extension to view the resulting widget.

### Example:

```lean
/-- A simple counter that can be incremented or decremented with some buttons. -/
meta def counter_widget {π α : Type} : component π α :=
component.ignore_props $ component.mk_simple int int 0 (λ _ x y, (x + y, none)) (λ _ s,
  h "div" [] [
    button "+" (1 : int),
    html.of_string $ to_string $ s,
    button "-" (-1)
  ]
)

#html counter_widget
```
-/
add_tactic_doc
  { Name := "#html", category := DocCategory.cmd, declNames := [`show_widget_cmd], tags := ["core", "widgets"] }

/-- The `add_decl_doc` command is used to add a doc string to an existing declaration.

```lean
def foo := 5

/--
Doc string for foo.
-/
add_decl_doc foo
```
-/
@[user_command]
unsafe def add_decl_doc_command (mi : interactive.decl_meta_info) (_ : parse <| tk "add_decl_doc") : parser Unit := do
  let n ← parser.ident
  let n ← resolve_constant n
  let some doc ← pure mi.doc_string | fail "add_decl_doc requires a doc string"
  add_doc_string n doc

add_tactic_doc
  { Name := "add_decl_doc", category := DocCategory.cmd, declNames := [`` add_decl_doc_command],
    tags := ["documentation"] }

