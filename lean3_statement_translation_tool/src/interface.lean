import prompting

open interactive lean.parser

/--!
Translates a statement to Lean code automatically using OpenAI Codex.

This command is not meant to be used directly, but rather through the `#translate?` command.
-/
@[user_command]
meta def translate_cmd (_ : parse $ tk "#translate ") : lean.parser unit := do
  s ← lean.parser.pexpr,
  let stmt := to_string s,
  trace sformat!"Translating {stmt} to Lean code ...\n" pure (),
  -- is there a safer way of operating within the `lean.parser` monad?
  translations ← tactic.unsafe_run_io $ get_translations stmt,
  suggest_strings translations

/--!
Translates a statement to Lean code **with documentation** automatically using OpenAI Codex.

This command is not meant to be used directly, but rather through the `#translate?` command.
-/
@[user_command]
meta def translate_with_docstring_cmd (_ : parse $ tk "#translate/") : lean.parser unit := do
  s ← lean.parser.pexpr,
  let stmt := to_string s,
  trace sformat!"Translating {stmt} to Lean code ...\n" pure (),
  -- is there a safer way of operating within the `lean.parser` monad?
  translations ← tactic.unsafe_run_io $ get_translations stmt,
  suggest_strings $ translations.map (λ t, sformat!"/-- {stmt} -/\n{t} :=\n  sorry")

/--!
Provides an interface to the `#translate ` and `#translate/` commands for automatic translation of mathematical statements to Lean code.

The two-step interface is to avoid triggering the expensive tactics at every keystroke.
-/
@[user_command]
meta def translate_help (_ : parse $ tk "translate?") : lean.parser unit := do
  trace "This tool uses OpenAI Codex to turn mathematical statements in natural language to Lean code.\n\n" pure (),
  stmt ← lean.parser.pexpr,
  let s := to_string stmt,
  trace sformat!"To start translating the sentence {s} into a Lean theorem," pure (),
  suggest_string $ "translate " ++ s,
  trace sformat!"\nTo start translating the sentence {s} into a Lean theorem with a docstring," pure (),
  suggest_string $ "translate/ " ++ s

/--!
A hole command that invokes the `#translate` command to automatically translate mathematical statements to Lean code.
-/
@[hole_command] meta def translate : hole_command := {
  name := "translate",
  descr := "Autoformalise to Lean code",
  action := λ ps, do
    [p] ← return ps | tactic.fail "Infer command failed, the hole must contain a single term",
    let s := to_string p,
    return [("#translate " ++ s, "Translation of " ++ s), ("translate/ " ++ s, "Translation of " ++ s ++ " with docstring")]
  }