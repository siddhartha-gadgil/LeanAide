import declaration_with_docstring

/-!
A list of theorems that will constitute the "fixed prompts" part of the full prompt to Codex.

This is not being used currently.
-/

/-- Every natural number is equal to itself. -/
theorem nat.all_eq_self : ∀ n : ℕ, n = n := sorry

/-- `0` is the smallest natural number. -/
theorem nat.zero_smallest : ∀ n, 0 < n := sorry


/-! The list of fixed prompts, automatically extracted from the theorems in this file.  -/
meta def fixed_prompts := declaration_with_docstring.module_decls

/-! TODO: The `fixed_prompts` will not be the same in any other file, 
    so there needs to be a way of storing them permanently. 
    
    Writing to and then subsequently reading from a `.json` file seems like the best option.

    If there are not a lot of fixed prompts, the list of `declaration_with_docstring`s can just be prepared manually.
     -/

run_cmd fixed_prompts >>= λ l, 
  tactic.trace $ l.map declaration_with_docstring.doc_string