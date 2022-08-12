/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
import Mathbin.Algebra.Group.ToAdditive
import Mathbin.Tactic.Lint.Frontend
import Mathbin.Tactic.Lint.Misc
import Mathbin.Tactic.Lint.Simp
import Mathbin.Tactic.Lint.TypeClasses

/-!
# Default linters

This file defines the list of linters that are run in mathlib CI. Not all linters are considered
"default" and run that way. A `linter` is marked as default if it is tagged with the `linter`
attribute.
-/


open Tactic

add_tactic_doc
  { Name := "linting commands", category := DocCategory.cmd,
    declNames := [`lint_cmd, `lint_mathlib_cmd, `lint_all_cmd, `list_linters], tags := ["linting"],
    description :=
      "User commands to spot common mistakes in the code\n\n* `#lint`: check all declarations in the current file\n* `#lint_mathlib`: check all declarations in mathlib (so excluding core or other projects,\n  and also excluding the current file)\n* `#lint_all`: check all declarations in the environment (the current file and all\n  imported files)\n\nThe following linters are run by default:\n1. `unused_arguments` checks for unused arguments in declarations.\n2. `def_lemma` checks whether a declaration is incorrectly marked as a def/lemma.\n3. `dup_namespce` checks whether a namespace is duplicated in the name of a declaration.\n4. `ge_or_gt` checks whether ≥/> is used in the declaration.\n5. `instance_priority` checks that instances that always apply have priority below default.\n6. `doc_blame` checks for missing doc strings on definitions and constants.\n7.  `has_inhabited_instance` checks whether every type has an associated `inhabited` instance.\n8.  `impossible_instance` checks for instances that can never fire.\n9.  `incorrect_type_class_argument` checks for arguments in [square brackets] that are not classes.\n10. `dangerous_instance` checks for instances that generate type-class problems with metavariables.\n11. `fails_quickly` tests that type-class inference ends (relatively) quickly when applied to\n    variables.\n12. `has_coe_variable` tests that there are no instances of type `has_coe α t` for a variable `α`.\n13. `inhabited_nonempty` checks for `inhabited` instance arguments that should be changed to\n    `nonempty`.\n14. `simp_nf` checks that the left-hand side of simp lemmas is in simp-normal form.\n15. `simp_var_head` checks that there are no variables as head symbol of left-hand sides of\n    simp lemmas.\n16. `simp_comm` checks that no commutativity lemmas (such as `add_comm`) are marked simp.\n17. `decidable_classical` checks for `decidable` hypotheses that are used in the proof of a\n    proposition but not in the statement, and could be removed using `classical`.\n    Theorems in the `decidable` namespace are exempt.\n18. `has_coe_to_fun` checks that every type that coerces to a function has a direct\n    `has_coe_to_fun` instance.\n19. `check_type` checks that the statement of a declaration is well-typed.\n20. `check_univs` checks that there are no bad `max u v` universe levels.\n21. `syn_taut` checks that declarations are not syntactic tautologies.\n22. `check_reducibility` checks whether non-instances with a class as type are reducible.\n23. `unprintable_interactive` checks that interactive tactics have parser documentation.\n24. `to_additive_doc` checks if additive versions of lemmas have documentation.\n\nThe following linters are not run by default:\n1. `doc_blame_thm`, checks for missing doc strings on lemmas and theorems.\n2. `explicit_vars_of_iff` checks if there are explicit variables used on both sides of an iff.\n\nThe command `#list_linters` prints a list of the names of all available linters.\n\nYou can append a `*` to any command (e.g. `#lint_mathlib*`) to omit the slow tests (4).\n\nYou can append a `-` to any command (e.g. `#lint_mathlib-`) to run a silent lint\nthat suppresses the output if all checks pass.\nA silent lint will fail if any test fails.\n\nYou can append a `+` to any command (e.g. `#lint_mathlib+`) to run a verbose lint\nthat reports the result of each linter, including  the successes.\n\nYou can append a sequence of linter names to any command to run extra tests, in addition to the\ndefault ones. e.g. `#lint doc_blame_thm` will run all default tests and `doc_blame_thm`.\n\nYou can append `only name1 name2 ...` to any command to run a subset of linters, e.g.\n`#lint only unused_arguments`\n\nYou can add custom linters by defining a term of type `linter` in the `linter` namespace.\nA linter defined with the name `linter.my_new_check` can be run with `#lint my_new_check`\nor `lint only my_new_check`.\nIf you add the attribute `@[linter]` to `linter.my_new_check` it will run by default.\n\nAdding the attribute `@[nolint doc_blame unused_arguments]` to a declaration\nomits it from only the specified linter checks." }

/-- The default linters used in mathlib CI. -/
unsafe def mathlib_linters : List Name := by
  run_tac
    let ls ← get_checks true [] false
    let ls := ls.map fun ⟨n, _⟩ => `linter ++ n
    exact (reflect ls)

