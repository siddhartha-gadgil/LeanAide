/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Testing.SlimCheck.Testable
import Mathbin.Data.List.Sort

/-!
## Finding counterexamples automatically using `slim_check`

A proposition can be tested by writing it out as:

```lean
example (xs : list ℕ) (w : ∃ x ∈ xs, x < 3) : ∀ y ∈ xs, y < 5 := by slim_check
-- ===================
-- Found problems!

-- xs := [0, 5]
-- x := 0
-- y := 5
-- -------------------

example (x : ℕ) (h : 2 ∣ x) : x < 100 := by slim_check
-- ===================
-- Found problems!

-- x := 258
-- -------------------

example (α : Type) (xs ys : list α) : xs ++ ys = ys ++ xs := by slim_check
-- ===================
-- Found problems!

-- α := ℤ
-- xs := [-4]
-- ys := [1]
-- -------------------

example : ∀ x ∈ [1,2,3], x < 4 := by slim_check
-- Success
```

In the first example, `slim_check` is called on the following goal:

```lean
xs : list ℕ,
h : ∃ (x : ℕ) (H : x ∈ xs), x < 3
⊢ ∀ (y : ℕ), y ∈ xs → y < 5
```

The local constants are reverted and an instance is found for
`testable (∀ (xs : list ℕ), (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))`.
The `testable` instance is supported by instances of `sampleable (list ℕ)`,
`decidable (x < 3)` and `decidable (y < 5)`. `slim_check` builds a
`testable` instance step by step with:

```
- testable (∀ (xs : list ℕ), (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))
                                     -: sampleable (list xs)
- testable ((∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))
- testable (∀ x ∈ xs, x < 3 → (∀ y ∈ xs, y < 5))
- testable (x < 3 → (∀ y ∈ xs, y < 5))
                                     -: decidable (x < 3)
- testable (∀ y ∈ xs, y < 5)
                                     -: decidable (y < 5)
```

`sampleable (list ℕ)` lets us create random data of type `list ℕ` in a way that
helps find small counter-examples.  Next, the test of the proposition
hinges on `x < 3` and `y < 5` to both be decidable. The
implication between the two could be tested as a whole but it would be
less informative. Indeed, if we generate lists that only contain numbers
greater than `3`, the implication will always trivially hold but we should
conclude that we haven't found meaningful examples. Instead, when `x < 3`
does not hold, we reject the example (i.e.  we do not count it toward
the 100 required positive examples) and we start over. Therefore, when
`slim_check` prints `Success`, it means that a hundred suitable lists
were found and successfully tested.

If no counter-examples are found, `slim_check` behaves like `admit`.

`slim_check` can also be invoked using `#eval`:

```lean
#eval slim_check.testable.check (∀ (α : Type) (xs ys : list α), xs ++ ys = ys ++ xs)
-- ===================
-- Found problems!

-- α := ℤ
-- xs := [-4]
-- ys := [1]
-- -------------------
```

For more information on writing your own `sampleable` and `testable`
instances, see `testing.slim_check.testable`.
-/


namespace Tactic.Interactive

open Tactic SlimCheck

initialize
  registerTraceClass.1 `slim_check.instance

initialize
  registerTraceClass.1 `slim_check.decoration

initialize
  registerTraceClass.1 `slim_check.discarded

initialize
  registerTraceClass.1 `slim_check.success

initialize
  registerTraceClass.1 `slim_check.shrink.steps

initialize
  registerTraceClass.1 `slim_check.shrink.candidates

open Expr

/-- Tree structure representing a `testable` instance. -/
unsafe inductive instance_tree
  | node : Name → expr → List instance_tree → instance_tree

/-- Gather information about a `testable` instance. Given
an expression of type `testable ?p`, gather the
name of the `testable` instances that it is built from
and the proposition that they test. -/
unsafe def summarize_instance : expr → tactic instance_tree
  | lam n bi d b => do
    let v ← mk_local' n bi d
    summarize_instance <| b v
  | e@(app f x) => do
    let quote.1 (Testableₓ (%%ₓp)) ← infer_type e
    let xs ← e.get_app_args.mmapFilter (try_core ∘ summarize_instance)
    pure <| instance_tree.node e p xs
  | e => do
    failed

/-- format a `instance_tree` -/
unsafe def instance_tree.to_format : instance_tree → tactic format
  | instance_tree.node n p xs => do
    let xs ← format.join <$> xs.mmap fun t => flip format.indent 2 <$> instance_tree.to_format t
    let ys ← f!"testable ({← p})"
    f!"+ {(← n)} :{(← format.indent ys 2)}
        {← xs}"

unsafe instance instance_tree.has_to_tactic_format : has_to_tactic_format instance_tree :=
  ⟨instance_tree.to_format⟩

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:66:50: missing argument
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- `slim_check` considers a proof goal and tries to generate examples
that would contradict the statement.

Let's consider the following proof goal.

```lean
xs : list ℕ,
h : ∃ (x : ℕ) (H : x ∈ xs), x < 3
⊢ ∀ (y : ℕ), y ∈ xs → y < 5
```

The local constants will be reverted and an instance will be found for
`testable (∀ (xs : list ℕ), (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))`.
The `testable` instance is supported by an instance of `sampleable (list ℕ)`,
`decidable (x < 3)` and `decidable (y < 5)`.

Examples will be created in ascending order of size (more or less)

The first counter-examples found will be printed and will result in an error:

```
===================
Found problems!

xs := [1, 28]
x := 1
y := 28
-------------------
```

If `slim_check` successfully tests 100 examples, it acts like
admit. If it gives up or finds a counter-example, it reports an error.

For more information on writing your own `sampleable` and `testable`
instances, see `testing.slim_check.testable`.

Optional arguments given with `slim_check_cfg`
* `num_inst` (default 100): number of examples to test properties with
* `max_size` (default 100): final size argument
* `enable_tracing` (default `ff`): enable the printing of discarded samples

Options:
* `set_option trace.slim_check.decoration true`: print the proposition with quantifier annotations
* `set_option trace.slim_check.discarded true`: print the examples discarded because they do not
  satisfy assumptions
* `set_option trace.slim_check.shrink.steps true`: trace the shrinking of counter-example
* `set_option trace.slim_check.shrink.candidates true`: print the lists of candidates considered
  when shrinking each variable
* `set_option trace.slim_check.instance true`: print the instances of `testable` being used to test
  the proposition
* `set_option trace.slim_check.success true`: print the tested samples that satisfy a property
-/
unsafe def slim_check (cfg : SlimCheckCfg := {  }) : tactic Unit := do
  let tgt ← retrieve <| tactic.revert_all >> target
  let tgt' := tactic.add_decorations tgt
  let cfg :=
    { cfg with traceDiscarded := cfg.traceDiscarded || is_trace_enabled_for `slim_check.discarded,
      traceShrink := cfg.traceShrink || is_trace_enabled_for `slim_check.shrink.steps,
      traceShrinkCandidates := cfg.traceShrinkCandidates || is_trace_enabled_for `slim_check.shrink.candidates,
      traceSuccess := cfg.traceSuccess || is_trace_enabled_for `slim_check.success }
  let inst ←
    mk_app `` testable [tgt'] >>= mk_instance <|>
        "./././Mathport/Syntax/Translate/Basic.lean:1143:38: in tactic.fail_macro: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
  let e ← mk_mapp `` testable.check [tgt, quote.1 cfg, tgt', inst]
  when_tracing `slim_check.decoration
      (← do
        dbg_trace "[testable decoration]
            {← tgt'}")
  when_tracing `slim_check.instance <| do
      let inst ← summarize_instance inst >>= pp
      ← do
          dbg_trace "
            [testable instance]{← format.indent inst 2}"
  let code ← eval_expr (Io PUnit) e
  unsafe_run_io code
  tactic.admit

end Tactic.Interactive

