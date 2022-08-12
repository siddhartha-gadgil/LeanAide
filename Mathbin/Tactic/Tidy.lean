/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Tactic.AutoCases
import Mathbin.Tactic.Chain
import Mathbin.Tactic.NormCast

namespace Tactic

namespace Tidy

/-- Tag interactive tactics (locally) with `[tidy]` to add them to the list of default tactics
called by `tidy`. -/
@[user_attribute]
unsafe def tidy_attribute : user_attribute where
  Name := `tidy
  descr := "A tactic that should be called by `tidy`."

add_tactic_doc
  { Name := "tidy", category := DocCategory.attr, declNames := [`tactic.tidy.tidy_attribute], tags := ["search"] }

unsafe def run_tactics : tactic Stringₓ := do
  let names ← attribute.get_instances `tidy
  first (names name_to_tactic) <|> fail "no @[tidy] tactics succeeded"

@[hint_tactic]
unsafe def ext1_wrapper : tactic Stringₓ := do
  let ng ← num_goals
  ext1 [] { NewGoals := new_goals.all }
  let ng' ← num_goals
  return <| if ng' > ng then "tactic.ext1 [] {new_goals := tactic.new_goals.all}" else "ext1"

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
unsafe def default_tactics : List (tactic Stringₓ) :=
  [reflexivity >> pure "refl", sorry >> pure "exact dec_trivial",
    (propositional_goal >> assumption) >> pure "assumption",
    intros1 >>= fun ns => pure ("intros " ++ (" ".intercalate <| ns.map fun e => e.toString)), auto_cases,
    sorry >> pure "apply_auto_param", sorry >> pure "dsimp at *", sorry >> pure "simp at *", ext1_wrapper,
    fsplit >> pure "fsplit", injections_and_clear >> pure "injections_and_clear",
    (propositional_goal >> sorry) >> pure "solve_by_elim", sorry >> pure "norm_cast", sorry >> pure "unfold_coes",
    sorry >> pure "unfold_aux", tidy.run_tactics]

unsafe structure cfg where
  trace_result : Bool := false
  trace_result_prefix : Stringₓ := "Try this: "
  tactics : List (tactic Stringₓ) := default_tactics

initialize
  registerTraceClass.1 `tidy

-- ./././Mathport/Syntax/Translate/Basic.lean:971:4: warning: unsupported notation `cfg
unsafe def core (cfg : cfg := {  }) : tactic (List Stringₓ) := do
  let results ← chain cfg.tactics
  when (cfg cfg.trace_result) <| trace (cfg ++ ", ".intercalate results)
  return results

end Tidy

unsafe def tidy (cfg : tidy.cfg := {  }) :=
  tactic.tidy.core cfg >> skip

namespace Interactive

setup_tactic_parser

/-- Use a variety of conservative tactics to solve goals.

`tidy?` reports back the tactic script it found. As an example
```lean
example : ∀ x : unit, x = unit.star :=
begin
  tidy? -- Prints the trace message: "Try this: intros x, exact dec_trivial"
end
```

The default list of tactics is stored in `tactic.tidy.default_tidy_tactics`.
This list can be overridden using `tidy { tactics := ... }`.
(The list must be a `list` of `tactic string`, so that `tidy?`
can report a usable tactic script.)

Tactics can also be added to the list by tagging them (locally) with the
`[tidy]` attribute. -/
unsafe def tidy (trace : parse <| optionalₓ (tk "?")) (cfg : tidy.cfg := {  }) :=
  tactic.tidy { cfg with trace_result := trace.isSome }

end Interactive

add_tactic_doc
  { Name := "tidy", category := DocCategory.tactic, declNames := [`tactic.interactive.tidy],
    tags := ["search", "Try this", "finishing"] }

/-- Invoking the hole command `tidy` ("Use `tidy` to complete the goal") runs the tactic of
the same name, replacing the hole with the tactic script `tidy` produces.
-/
@[hole_command]
unsafe def tidy_hole_cmd : hole_command where
  Name := "tidy"
  descr := "Use `tidy` to complete the goal."
  action := fun _ => do
    let script ← tidy.core
    return [("begin " ++ ", ".intercalate script ++ " end", "by tidy")]

add_tactic_doc
  { Name := "tidy", category := DocCategory.hole_cmd, declNames := [`tactic.tidy_hole_cmd], tags := ["search"] }

end Tactic

