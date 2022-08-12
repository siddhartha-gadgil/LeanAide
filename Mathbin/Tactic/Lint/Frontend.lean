/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
import Mathbin.Meta.RbMap
import Mathbin.Tactic.Lint.Basic

/-!
# Linter frontend and commands

This file defines the linter commands which spot common mistakes in the code.
* `#lint`: check all declarations in the current file
* `#lint_mathlib`: check all declarations in mathlib (so excluding core or other projects,
  and also excluding the current file)
* `#lint_all`: check all declarations in the environment (the current file and all
  imported files)

For a list of default / non-default linters, see the "Linting Commands" user command doc entry.

The command `#list_linters` prints a list of the names of all available linters.

You can append a `*` to any command (e.g. `#lint_mathlib*`) to omit the slow tests (4).

You can append a `-` to any command (e.g. `#lint_mathlib-`) to run a silent lint
that suppresses the output if all checks pass.
A silent lint will fail if any test fails.

You can append a `+` to any command (e.g. `#lint_mathlib+`) to run a verbose lint
that reports the result of each linter, including  the successes.

You can append a sequence of linter names to any command to run extra tests, in addition to the
default ones. e.g. `#lint doc_blame_thm` will run all default tests and `doc_blame_thm`.

You can append `only name1 name2 ...` to any command to run a subset of linters, e.g.
`#lint only unused_arguments`

You can add custom linters by defining a term of type `linter` in the `linter` namespace.
A linter defined with the name `linter.my_new_check` can be run with `#lint my_new_check`
or `lint only my_new_check`.
If you add the attribute `@[linter]` to `linter.my_new_check` it will run by default.

Adding the attribute `@[nolint doc_blame unused_arguments]` to a declaration
omits it from only the specified linter checks.

## Tags

sanity check, lint, cleanup, command, tactic
-/


open Tactic Expr Native

setup_tactic_parser

/-- Verbosity for the linter output.
* `low`: only print failing checks, print nothing on success.
* `medium`: only print failing checks, print confirmation on success.
* `high`: print output of every check.
-/
inductive LintVerbosity
  | low
  | medium
  | high
  deriving DecidableEq, Inhabited

/-- `get_checks slow extra use_only` produces a list of linters.
`extras` is a list of names that should resolve to declarations with type `linter`.
If `use_only` is true, it only uses the linters in `extra`.
Otherwise, it uses all linters in the environment tagged with `@[linter]`.
If `slow` is false, it only uses the fast default tests. -/
unsafe def get_checks (slow : Bool) (extra : List Name) (use_only : Bool) : tactic (List (Name × linter)) := do
  let default ← if use_only then return [] else attribute.get_instances `linter >>= get_linters
  let default := if slow then default else default.filter fun l => l.2.is_fast
  List.append default <$> get_linters extra

/-- `lint_core all_decls non_auto_decls checks` applies the linters `checks` to the list of
declarations.
If `auto_decls` is false for a linter (default) the linter is applied to `non_auto_decls`.
If `auto_decls` is true, then it is applied to `all_decls`.
The resulting list has one element for each linter, containing the linter as
well as a map from declaration name to warning.
-/
unsafe def lint_core (all_decls non_auto_decls : List declaration) (checks : List (Name × linter)) :
    tactic (List (Name × linter × rb_map Name Stringₓ)) := do
  checks fun ⟨linter_name, linter⟩ => do
      let test_decls := if linter then all_decls else non_auto_decls
      let test_decls ← test_decls fun decl => should_be_linted linter_name decl
      let s ← read
      let results :=
        test_decls fun decl =>
          Prod.mk decl <|
            match linter decl s with
            | result.success w _ => w
            | result.exception msg _ _ => some <| "LINTER FAILED:\n" ++ msg "(no message)" fun msg => toString <| msg ()
      let results :=
        results
          (fun (results : rb_map Name Stringₓ) warning =>
            match warning with
            | (decl_name, some w) => results decl_name w
            | (_, none) => results)
          mk_rb_map
      pure (linter_name, linter, results)

/-- Sorts a map with declaration keys as names by line number. -/
unsafe def sort_results {α} (e : environment) (results : rb_map Name α) : List (Name × α) :=
  List.reverse <|
    rb_lmap.values <|
      rb_lmap.of_list <|
        (results.fold []) fun decl linter_warning results =>
          (((e.decl_pos decl).getOrElse ⟨0, 0⟩).line, (decl, linter_warning)) :: results

/-- Formats a linter warning as `#check` command with comment. -/
unsafe def print_warning (decl_name : Name) (warning : Stringₓ) : format :=
  "#check @" ++ to_fmt decl_name ++ " /- " ++ warning ++ " -/"

private def workflow_command_replacements : Charₓ → Stringₓ
  | '%' => "%25"
  | '\n' => "%0A"
  | c => toString c

/-- Escape characters that may not be used in a workflow commands, following
https://github.com/actions/toolkit/blob/7257597d731b34d14090db516d9ea53439300e98/packages/core/src/command.ts#L92-L105
-/
def escapeWorkflowCommand (s : Stringₓ) : Stringₓ :=
  "".intercalate <| s.toList.map workflowCommandReplacements

/-- Prints a workflow command to emit an error understood by github in an actions workflow.
This enables CI to tag the parts of the file where linting failed with annotations, and makes it
easier for mathlib contributors to see what needs fixing.
See https://docs.github.com/en/actions/learn-github-actions/workflow-commands-for-github-actions#setting-an-error-message
-/
unsafe def print_workflow_command (env : environment) (linter_name decl_name : Name) (warning : Stringₓ) :
    Option Stringₓ := do
  let po ← env.decl_pos decl_name
  let ol ← env.decl_olean decl_name
  return <|
      ((s! "
            ::error file={ol },line={po },col={po},title=") ++
          s! "Warning from {linter_name} linter::") ++
        s!"{(escapeWorkflowCommand <| toString decl_name)} - {escapeWorkflowCommand warning}"

/-- Formats a map of linter warnings using `print_warning`, sorted by line number. -/
unsafe def print_warnings (env : environment) (emit_workflow_commands : Bool) (linter_name : Name)
    (results : rb_map Name Stringₓ) : format :=
  format.intercalate format.line <|
    (sort_results env results).map fun ⟨decl_name, warning⟩ =>
      let form := print_warning decl_name warning
      if emit_workflow_commands then form ++ (print_workflow_command env linter_name decl_name warning).getOrElse ""
      else form

/-- Formats a map of linter warnings grouped by filename with `-- filename` comments.
The first `drop_fn_chars` characters are stripped from the filename.
-/
unsafe def grouped_by_filename (e : environment) (results : rb_map Name Stringₓ) (drop_fn_chars := 0)
    (formatter : rb_map Name Stringₓ → format) : format :=
  let results :=
    (results.fold (rb_map.mk Stringₓ (rb_map Name Stringₓ))) fun decl_name linter_warning results =>
      let fn := (e.decl_olean decl_name).getOrElse ""
      results.insert fn (((results.find fn).getOrElse mk_rb_map).insert decl_name linter_warning)
  let l :=
    results.toList.reverse.map fun ⟨fn, results⟩ =>
      ("-- " ++ fn.popn drop_fn_chars ++ "\n" ++ formatter results : format)
  format.intercalate "\n\n" l ++ "\n"

/-- Formats the linter results as Lean code with comments and `#check` commands.
-/
unsafe def format_linter_results (env : environment) (results : List (Name × linter × rb_map Name Stringₓ))
    (decls non_auto_decls : List declaration) (group_by_filename : Option ℕ) (where_desc : Stringₓ) (slow : Bool)
    (verbose : LintVerbosity) (num_linters : ℕ)
    -- whether to include codes understood by github to create file annotations
    (emit_workflow_commands : Bool := false) :
    format := do
  let formatted_results :=
    results.map fun ⟨linter_name, linter, results⟩ =>
      let report_str : format := to_fmt "/- The `" ++ to_fmt linter_name ++ "` linter reports: -/\n"
      if ¬results.Empty then
        let warnings :=
          match group_by_filename with
          | none => print_warnings env emit_workflow_commands linter_name results
          | some dropped =>
            grouped_by_filename env results dropped (print_warnings env emit_workflow_commands linter_name)
        report_str ++ "/- " ++ linter.errors_found ++ " -/\n" ++ warnings ++ "\n"
      else if verbose = LintVerbosity.high then "/- OK: " ++ linter.no_errors_found ++ " -/" else format.nil
  let s := format.intercalate "\n" (formatted_results.filter fun f => ¬f.is_nil)
  let s :=
    if verbose = LintVerbosity.low then s
    else
      (f! "/- Checking {non_auto_decls.length} declarations (plus {(decls.length -
            non_auto_decls.length)} automatically generated ones) {where_desc } with {num_linters} linters -/
          
          ") ++
        s
  let s := if slow then s else s ++ "/- (slow tests skipped) -/\n"
  s

/-- The common denominator of `#lint[|mathlib|all]`.
The different commands have different configurations for `l`,
`group_by_filename` and `where_desc`.
If `slow` is false, doesn't do the checks that take a lot of time.
If `verbose` is false, it will suppress messages from passing checks.
By setting `checks` you can customize which checks are performed.

Returns a `name_set` containing the names of all declarations that fail any check in `check`,
and a `format` object describing the failures. -/
unsafe def lint_aux (decls : List declaration) (group_by_filename : Option ℕ) (where_desc : Stringₓ) (slow : Bool)
    (verbose : LintVerbosity) (checks : List (Name × linter)) : tactic (name_set × format) := do
  let e ← get_env
  let non_auto_decls := decls.filter fun d => ¬d.is_auto_or_internal e
  let results ← lint_core decls non_auto_decls checks
  let s := format_linter_results e results decls non_auto_decls group_by_filename where_desc slow verbose checks.length
  let ns :=
    name_set.of_list do
      let (_, _, rs) ← results
      rs
  pure (ns, s)

/-- Return the message printed by `#lint` and a `name_set` containing all declarations that fail. -/
unsafe def lint (slow : Bool := true) (verbose : LintVerbosity := LintVerbosity.medium) (extra : List Name := [])
    (use_only : Bool := false) : tactic (name_set × format) := do
  let checks ← get_checks slow extra use_only
  let e ← get_env
  let l := e.filter fun d => e.in_current_file d.to_name
  lint_aux l none "in the current file" slow verbose checks

/-- Returns the declarations in the folder `proj_folder`. -/
unsafe def lint_project_decls (proj_folder : Stringₓ) : tactic (List declaration) := do
  let e ← get_env
  pure <| e fun d => e proj_folder d

/-- Returns the linter message by running the linter on all declarations in project `proj_name` in
folder `proj_folder`. It also returns a `name_set` containing all declarations that fail.

To add a linter command for your own project, write
```
open lean.parser lean tactic interactive
@[user_command] meta def lint_my_project_cmd (_ : parse $ tk "#lint_my_project") : parser unit :=
do str ← get_project_dir n k, lint_cmd_aux (@lint_project str "my project")
```
Here `n` is the name of any declaration in the project (like `` `lint_my_project_cmd`` and `k` is
the number of characters in the filename of `n` *after* the `src/` directory
(so e.g. the number of characters in `tactic/lint/frontend.lean`).
Warning: the linter will not work in the file where `n` is declared.
-/
unsafe def lint_project (proj_folder proj_name : Stringₓ) (slow : Bool := true)
    (verbose : LintVerbosity := LintVerbosity.medium) (extra : List Name := []) (use_only : Bool := false) :
    tactic (name_set × format) := do
  let checks ← get_checks slow extra use_only
  let decls ← lint_project_decls proj_folder
  lint_aux decls proj_folder ("in " ++ proj_name ++ " (only in imported files)") slow verbose checks

/-- Return the message printed by `#lint_all` and a `name_set` containing all declarations
that fail. -/
unsafe def lint_all (slow : Bool := true) (verbose : LintVerbosity := LintVerbosity.medium) (extra : List Name := [])
    (use_only : Bool := false) : tactic (name_set × format) := do
  let checks ← get_checks slow extra use_only
  let e ← get_env
  let l := e.get_decls
  lint_aux l (some 0) "in all imported files (including this one)" slow verbose checks

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `«expr *»
/-- Parses an optional `only`, followed by a sequence of zero or more identifiers.
Prepends `linter.` to each of these identifiers. -/
unsafe def parse_lint_additions : parser (Bool × List Name) :=
  Prod.mk <$> only_flag <*> List.map (name.append `linter) <$> «expr *» ident

/-- Parses a "-" or "+", returning `lint_verbosity.low` or `lint_verbosity.high` respectively,
or returns `none`.
-/
unsafe def parse_verbosity : parser (Option LintVerbosity) :=
  tk "-" >> return LintVerbosity.low <|> tk "+" >> return LintVerbosity.high <|> return none

/-- The common denominator of `lint_cmd`, `lint_mathlib_cmd`, `lint_all_cmd` -/
unsafe def lint_cmd_aux (scope : Bool → LintVerbosity → List Name → Bool → tactic (name_set × format)) : parser Unit :=
  do
  let verbosity ← parse_verbosity
  let fast_only ← optionalₓ (tk "*")
  let verbosity
    ←-- allow either order of *-
        if verbosity.isSome then return verbosity
      else parse_verbosity
  let verbosity := verbosity.getOrElse LintVerbosity.medium
  let (use_only, extra) ← parse_lint_additions
  let (failed, s) ← scope fast_only.isNone verbosity extra use_only
  when ¬s <| trace s
  when (verbosity = LintVerbosity.low ∧ ¬failed) <| fail "Linting did not succeed"
  when (verbosity = LintVerbosity.medium ∧ failed) <| trace "/- All linting checks passed! -/"

/-- The command `#lint` at the bottom of a file will warn you about some common mistakes
in that file. Usage: `#lint`, `#lint linter_1 linter_2`, `#lint only linter_1 linter_2`.
`#lint-` will suppress the output if all checks pass.
`#lint+` will enable verbose output.

Use the command `#list_linters` to see all available linters. -/
@[user_command]
unsafe def lint_cmd (_ : parse <| tk "#lint") : parser Unit :=
  lint_cmd_aux @lint

/-- The command `#lint_mathlib` checks all of mathlib for certain mistakes.
Usage: `#lint_mathlib`, `#lint_mathlib linter_1 linter_2`, `#lint_mathlib only linter_1 linter_2`.
`#lint_mathlib-` will suppress the output if all checks pass.
`lint_mathlib+` will enable verbose output.

Use the command `#list_linters` to see all available linters. -/
@[user_command]
unsafe def lint_mathlib_cmd (_ : parse <| tk "#lint_mathlib") : parser Unit := do
  let str ← get_mathlib_dir
  lint_cmd_aux (@lint_project str "mathlib")

/-- The command `#lint_all` checks all imported files for certain mistakes.
Usage: `#lint_all`, `#lint_all linter_1 linter_2`, `#lint_all only linter_1 linter_2`.
`#lint_all-` will suppress the output if all checks pass.
`lint_all+` will enable verbose output.

Use the command `#list_linters` to see all available linters. -/
@[user_command]
unsafe def lint_all_cmd (_ : parse <| tk "#lint_all") : parser Unit :=
  lint_cmd_aux @lint_all

/-- The command `#list_linters` prints a list of all available linters. -/
@[user_command]
unsafe def list_linters (_ : parse <| tk "#list_linters") : parser Unit := do
  let env ← get_env
  let ns :=
    env.decl_filter_map fun dcl =>
      if dcl.to_name.getPrefix = `linter && dcl.type = quote.1 linter then some dcl.to_name else none
  trace "Available linters:\n  linters marked with (*) are in the default lint set\n"
  ns fun n => do
      let b ← has_attribute' `linter n
      trace <| n ++ if b then " (*)" else ""

/-- Invoking the hole command `lint` ("Find common mistakes in current file") will print text that
indicates mistakes made in the file above the command. It is equivalent to copying and pasting the
output of `#lint`. On large files, it may take some time before the output appears.
-/
@[hole_command]
unsafe def lint_hole_cmd : hole_command where
  Name := "Lint"
  descr := "Lint: Find common mistakes in current file."
  action := fun es => do
    let (_, s) ← lint
    return [(s, "")]

add_tactic_doc { Name := "Lint", category := DocCategory.hole_cmd, declNames := [`lint_hole_cmd], tags := ["linting"] }

