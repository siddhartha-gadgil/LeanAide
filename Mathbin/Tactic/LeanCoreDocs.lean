/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Bryan Gin-ge Chen, Robert Y. Lewis, Scott Morrison
-/
import Mathbin.Tactic.DocCommands

/-!

# Core tactic documentation

This file adds the majority of the interactive tactics from core Lean (i.e. pre-mathlib) to
the API documentation.

## TODO

* Make a PR to core changing core docstrings to the docstrings below,
and also changing the docstrings of `cc`, `simp` and `conv` to the ones
already in the API docs.

* SMT tactics are currently not documented.

* `rsimp` and `constructor_matching` are currently not documented.

* `dsimp` deserves better documentation.
-/


add_tactic_doc
  { Name := "abstract", category := DocCategory.tactic, declNames := [`tactic.interactive.abstract],
    tags := ["core", "proof extraction"] }

/-- Proves a goal of the form `s = t` when `s` and `t` are expressions built up out of a binary
operation, and equality can be proved using associativity and commutativity of that operation. -/
add_tactic_doc
  { Name := "ac_refl", category := DocCategory.tactic,
    declNames := [`tactic.interactive.ac_refl, `tactic.interactive.ac_reflexivity],
    tags := ["core", "lemma application", "finishing"] }

add_tactic_doc
  { Name := "all_goals", category := DocCategory.tactic, declNames := [`tactic.interactive.all_goals],
    tags := ["core", "goal management"] }

add_tactic_doc
  { Name := "any_goals", category := DocCategory.tactic, declNames := [`tactic.interactive.any_goals],
    tags := ["core", "goal management"] }

add_tactic_doc
  { Name := "apply", category := DocCategory.tactic, declNames := [`tactic.interactive.apply],
    tags := ["core", "basic", "lemma application"] }

add_tactic_doc
  { Name := "apply_auto_param", category := DocCategory.tactic, declNames := [`tactic.interactive.apply_auto_param],
    tags := ["core", "lemma application"] }

add_tactic_doc
  { Name := "apply_instance", category := DocCategory.tactic, declNames := [`tactic.interactive.apply_instance],
    tags := ["core", "type class"] }

add_tactic_doc
  { Name := "apply_opt_param", category := DocCategory.tactic, declNames := [`tactic.interactive.apply_opt_param],
    tags := ["core", "lemma application"] }

add_tactic_doc
  { Name := "apply_with", category := DocCategory.tactic, declNames := [`tactic.interactive.apply_with],
    tags := ["core", "lemma application"] }

add_tactic_doc
  { Name := "assume", category := DocCategory.tactic, declNames := [`tactic.interactive.assume],
    tags := ["core", "logic"] }

add_tactic_doc
  { Name := "assumption", category := DocCategory.tactic, declNames := [`tactic.interactive.assumption],
    tags := ["core", "basic", "finishing"] }

add_tactic_doc
  { Name := "assumption'", category := DocCategory.tactic, declNames := [`tactic.interactive.assumption'],
    tags := ["core", "goal management"] }

add_tactic_doc
  { Name := "async", category := DocCategory.tactic, declNames := [`tactic.interactive.async],
    tags := ["core", "goal management", "combinator", "proof extraction"] }

/-- `by_cases p` splits the main goal into two cases, assuming `h : p` in the first branch, and
`h : ¬ p` in the second branch. You can specify the name of the new hypothesis using the syntax
`by_cases h : p`.

If `p` is not already decidable, `by_cases` will use the instance `classical.prop_decidable p`.
-/
add_tactic_doc
  { Name := "by_cases", category := DocCategory.tactic, declNames := [`tactic.interactive.by_cases],
    tags := ["core", "basic", "logic", "case bashing"] }

/-- If the target of the main goal is a proposition `p`, `by_contra h` reduces the goal to proving
`false` using the additional hypothesis `h : ¬ p`. If `h` is omitted, a name is generated
automatically.

This tactic requires that `p` is decidable. To ensure that all propositions are decidable via
classical reasoning, use `open_locale classical`
(or `local attribute [instance, priority 10] classical.prop_decidable` if you are not using
mathlib).
-/
add_tactic_doc
  { Name := "by_contra / by_contradiction", category := DocCategory.tactic,
    declNames := [`tactic.interactive.by_contra, `tactic.interactive.by_contradiction], tags := ["core", "logic"] }

add_tactic_doc
  { Name := "case", category := DocCategory.tactic, declNames := [`tactic.interactive.case],
    tags := ["core", "goal management"] }

add_tactic_doc
  { Name := "cases", category := DocCategory.tactic, declNames := [`tactic.interactive.cases],
    tags := ["core", "basic", "induction"] }

/-- `cases_matching p` applies the `cases` tactic to a hypothesis `h : type`
if `type` matches the pattern `p`.

`cases_matching [p_1, ..., p_n]` applies the `cases` tactic to a hypothesis `h : type`
if `type` matches one of the given patterns.

`cases_matching* p` is a more efficient and compact version
of `focus1 { repeat { cases_matching p } }`.
It is more efficient because the pattern is compiled once.

`casesm` is shorthand for `cases_matching`.

Example: The following tactic destructs all conjunctions and disjunctions in the current context.
```
cases_matching* [_ ∨ _, _ ∧ _]
```
-/
add_tactic_doc
  { Name := "cases_matching / casesm", category := DocCategory.tactic,
    declNames := [`tactic.interactive.cases_matching, `tactic.interactive.casesm],
    tags := ["core", "induction", "context management"] }

/-- * `cases_type I` applies the `cases` tactic to a hypothesis `h : (I ...)`
* `cases_type I_1 ... I_n` applies the `cases` tactic to a hypothesis
  `h : (I_1 ...)` or ... or `h : (I_n ...)`
* `cases_type* I` is shorthand for `focus1 { repeat { cases_type I } }`
* `cases_type! I` only applies `cases` if the number of resulting subgoals is <= 1.

Example: The following tactic destructs all conjunctions and disjunctions in the current context.
```
cases_type* or and
```
-/
add_tactic_doc
  { Name := "cases_type", category := DocCategory.tactic, declNames := [`tactic.interactive.cases_type],
    tags := ["core", "induction", "context management"] }

add_tactic_doc
  { Name := "change", category := DocCategory.tactic, declNames := [`tactic.interactive.change],
    tags := ["core", "basic", "renaming"] }

add_tactic_doc
  { Name := "clear", category := DocCategory.tactic, declNames := [`tactic.interactive.clear],
    tags := ["core", "context management"] }

/-- Close goals of the form `n ≠ m` when `n` and `m` have type `nat`, `char`, `string`, `int`
or `fin sz`, and they are literals. It also closes goals of the form `n < m`, `n > m`, `n ≤ m` and
`n ≥ m` for `nat`. If the goal is of the form `n = m`, then it tries to close it using reflexivity.

In mathlib, consider using `norm_num` instead for numeric types.
-/
add_tactic_doc
  { Name := "comp_val", category := DocCategory.tactic, declNames := [`tactic.interactive.comp_val],
    tags := ["core", "arithmetic"] }

/-- The `congr` tactic attempts to identify both sides of an equality goal `A = B`,
leaving as new goals the subterms of `A` and `B` which are not definitionally equal.
Example: suppose the goal is `x * f y = g w * f z`. Then `congr` will produce two goals:
`x = g w` and `y = z`.

If `x y : t`, and an instance `subsingleton t` is in scope, then any goals of the form
`x = y` are solved automatically.

Note that `congr` can be over-aggressive at times; the `congr'` tactic in mathlib
provides a more refined approach, by taking a parameter that limits the recursion depth.
-/
add_tactic_doc
  { Name := "congr", category := DocCategory.tactic, declNames := [`tactic.interactive.congr],
    tags := ["core", "congruence"] }

add_tactic_doc
  { Name := "constructor", category := DocCategory.tactic, declNames := [`tactic.interactive.constructor],
    tags := ["core", "logic"] }

add_tactic_doc
  { Name := "contradiction", category := DocCategory.tactic, declNames := [`tactic.interactive.contradiction],
    tags := ["core", "basic", "finishing"] }

add_tactic_doc
  { Name := "delta", category := DocCategory.tactic, declNames := [`tactic.interactive.delta],
    tags := ["core", "simplification"] }

add_tactic_doc
  { Name := "destruct", category := DocCategory.tactic, declNames := [`tactic.interactive.destruct],
    tags := ["core", "induction"] }

add_tactic_doc
  { Name := "done", category := DocCategory.tactic, declNames := [`tactic.interactive.done],
    tags := ["core", "goal management"] }

add_tactic_doc
  { Name := "dsimp", category := DocCategory.tactic, declNames := [`tactic.interactive.dsimp],
    tags := ["core", "simplification"] }

add_tactic_doc
  { Name := "dunfold", category := DocCategory.tactic, declNames := [`tactic.interactive.dunfold],
    tags := ["core", "simplification"] }

add_tactic_doc
  { Name := "eapply", category := DocCategory.tactic, declNames := [`tactic.interactive.eapply],
    tags := ["core", "lemma application"] }

add_tactic_doc
  { Name := "econstructor", category := DocCategory.tactic, declNames := [`tactic.interactive.econstructor],
    tags := ["core", "logic"] }

/-- A variant of `rw` that uses the unifier more aggressively, unfolding semireducible definitions.
-/
add_tactic_doc
  { Name := "erewrite / erw", category := DocCategory.tactic,
    declNames := [`tactic.interactive.erewrite, `tactic.interactive.erw], tags := ["core", "rewriting"] }

add_tactic_doc
  { Name := "exact", category := DocCategory.tactic, declNames := [`tactic.interactive.exact],
    tags := ["core", "basic", "finishing"] }

add_tactic_doc
  { Name := "exacts", category := DocCategory.tactic, declNames := [`tactic.interactive.exacts],
    tags := ["core", "finishing"] }

add_tactic_doc
  { Name := "exfalso", category := DocCategory.tactic, declNames := [`tactic.interactive.exfalso],
    tags := ["core", "basic", "logic"] }

/-- `existsi e` will instantiate an existential quantifier in the target with `e` and leave the
instantiated body as the new target. More generally, it applies to any inductive type with one
constructor and at least two arguments, applying the constructor with `e` as the first argument
and leaving the remaining arguments as goals.

`existsi [e₁, ..., eₙ]` iteratively does the same for each expression in the list.

Note: in mathlib, the `use` tactic is an equivalent tactic which sometimes is smarter with
unification.
-/
add_tactic_doc
  { Name := "existsi", category := DocCategory.tactic, declNames := [`tactic.interactive.existsi],
    tags := ["core", "logic"] }

add_tactic_doc
  { Name := "fail_if_success", category := DocCategory.tactic, declNames := [`tactic.interactive.fail_if_success],
    tags := ["core", "testing", "combinator"] }

add_tactic_doc
  { Name := "fapply", category := DocCategory.tactic, declNames := [`tactic.interactive.fapply],
    tags := ["core", "lemma application"] }

add_tactic_doc
  { Name := "focus", category := DocCategory.tactic, declNames := [`tactic.interactive.focus],
    tags := ["core", "goal management", "combinator"] }

add_tactic_doc
  { Name := "from", category := DocCategory.tactic, declNames := [`tactic.interactive.from],
    tags := ["core", "finishing"] }

/-- Apply function extensionality and introduce new hypotheses.
The tactic `funext` will keep applying new the `funext` lemma until the goal target is not reducible
to
```
  |-  ((fun x, ...) = (fun x, ...))
```
The variant `funext h₁ ... hₙ` applies `funext` `n` times, and uses the given identifiers to name
the new hypotheses.

Note also the mathlib tactic `ext`, which applies as many extensionality lemmas as possible.
-/
add_tactic_doc
  { Name := "funext", category := DocCategory.tactic, declNames := [`tactic.interactive.funext],
    tags := ["core", "logic"] }

add_tactic_doc
  { Name := "generalize", category := DocCategory.tactic, declNames := [`tactic.interactive.generalize],
    tags := ["core", "context management"] }

add_tactic_doc
  { Name := "guard_hyp", category := DocCategory.tactic, declNames := [`tactic.interactive.guard_hyp],
    tags := ["core", "testing", "context management"] }

add_tactic_doc
  { Name := "guard_target", category := DocCategory.tactic, declNames := [`tactic.interactive.guard_target],
    tags := ["core", "testing", "goal management"] }

add_tactic_doc
  { Name := "have", category := DocCategory.tactic, declNames := [`tactic.interactive.have],
    tags := ["core", "basic", "context management"] }

add_tactic_doc
  { Name := "induction", category := DocCategory.tactic, declNames := [`tactic.interactive.induction],
    tags := ["core", "basic", "induction"] }

add_tactic_doc
  { Name := "injection", category := DocCategory.tactic, declNames := [`tactic.interactive.injection],
    tags := ["core", "structures", "induction"] }

add_tactic_doc
  { Name := "injections", category := DocCategory.tactic, declNames := [`tactic.interactive.injections],
    tags := ["core", "structures", "induction"] }

/-- If the current goal is a Pi/forall `∀ x : t, u` (resp. `let x := t in u`) then `intro` puts
`x : t` (resp. `x := t`) in the local context. The new subgoal target is `u`.

If the goal is an arrow `t → u`, then it puts `h : t` in the local context and the new goal
target is `u`.

If the goal is neither a Pi/forall nor begins with a let binder, the tactic `intro` applies the
tactic `whnf` until an introduction can be applied or the goal is not head reducible. In the latter
case, the tactic fails.

The variant `intro z` uses the identifier `z` to name the new hypothesis.

The variant `intros` will keep introducing new hypotheses until the goal target is not a Pi/forall
or let binder.

The variant `intros h₁ ... hₙ` introduces `n` new hypotheses using the given identifiers to name
them.
-/
add_tactic_doc
  { Name := "intro / intros", category := DocCategory.tactic,
    declNames := [`tactic.interactive.intro, `tactic.interactive.intros], tags := ["core", "basic", "logic"] }

add_tactic_doc
  { Name := "introv", category := DocCategory.tactic, declNames := [`tactic.interactive.introv],
    tags := ["core", "logic"] }

add_tactic_doc
  { Name := "iterate", category := DocCategory.tactic, declNames := [`tactic.interactive.iterate],
    tags := ["core", "combinator"] }

/-- `left` applies the first constructor when the type of the target is an inductive data type with
two constructors.

Similarly, `right` applies the second constructor.
-/
add_tactic_doc
  { Name := "left / right", category := DocCategory.tactic,
    declNames := [`tactic.interactive.left, `tactic.interactive.right], tags := ["core", "basic", "logic"] }

/-- `let h : t := p` adds the hypothesis `h : t := p` to the current goal if `p` a term of type `t`.
If `t` is omitted, it will be inferred.

`let h : t` adds the hypothesis `h : t := ?M` to the current goal and opens a new subgoal `?M : t`.
The new subgoal becomes the main goal. If `t` is omitted, it will be replaced by a fresh
metavariable.

If `h` is omitted, the name `this` is used.

Note the related mathlib tactic `set a := t with h`, which adds the hypothesis `h : a = t` to
the local context and replaces `t` with `a` everywhere it can.
-/
add_tactic_doc
  { Name := "let", category := DocCategory.tactic, declNames := [`tactic.interactive.let],
    tags := ["core", "basic", "logic", "context management"] }

add_tactic_doc
  { Name := "mapply", category := DocCategory.tactic, declNames := [`tactic.interactive.mapply],
    tags := ["core", "lemma application"] }

add_tactic_doc
  { Name := "match_target", category := DocCategory.tactic, declNames := [`tactic.interactive.match_target],
    tags := ["core", "testing", "goal management"] }

add_tactic_doc
  { Name := "refine", category := DocCategory.tactic, declNames := [`tactic.interactive.refine],
    tags := ["core", "basic", "lemma application"] }

/-- This tactic applies to a goal whose target has the form `t ~ u` where `~` is a reflexive relation,
that is, a relation which has a reflexivity lemma tagged with the attribute `[refl]`.
The tactic checks whether `t` and `u` are definitionally equal and then solves the goal.
-/
add_tactic_doc
  { Name := "refl / reflexivity", category := DocCategory.tactic,
    declNames := [`tactic.interactive.refl, `tactic.interactive.reflexivity], tags := ["core", "basic", "finishing"] }

add_tactic_doc
  { Name := "rename", category := DocCategory.tactic, declNames := [`tactic.interactive.rename],
    tags := ["core", "renaming"] }

add_tactic_doc
  { Name := "repeat", category := DocCategory.tactic, declNames := [`tactic.interactive.repeat],
    tags := ["core", "combinator"] }

add_tactic_doc
  { Name := "revert", category := DocCategory.tactic, declNames := [`tactic.interactive.revert],
    tags := ["core", "context management", "goal management"] }

/-- `rw e` applies an equation or iff `e` as a rewrite rule to the main goal. If `e` is preceded by
left arrow (`←` or `<-`), the rewrite is applied in the reverse direction. If `e` is a defined
constant, then the equational lemmas associated with `e` are used. This provides a convenient
way to unfold `e`.

`rw [e₁, ..., eₙ]` applies the given rules sequentially.

`rw e at l` rewrites `e` at location(s) `l`, where `l` is either `*` or a list of hypotheses
in the local context. In the latter case, a turnstile `⊢` or `|-` can also be used, to signify
the target of the goal.

`rewrite` is synonymous with `rw`.
-/
add_tactic_doc
  { Name := "rw / rewrite", category := DocCategory.tactic,
    declNames := [`tactic.interactive.rw, `tactic.interactive.rewrite], tags := ["core", "basic", "rewriting"] }

add_tactic_doc
  { Name := "rwa", category := DocCategory.tactic, declNames := [`tactic.interactive.rwa],
    tags := ["core", "rewriting"] }

add_tactic_doc
  { Name := "show", category := DocCategory.tactic, declNames := [`tactic.interactive.show],
    tags := ["core", "goal management", "renaming"] }

add_tactic_doc
  { Name := "simp_intros", category := DocCategory.tactic, declNames := [`tactic.interactive.simp_intros],
    tags := ["core", "simplification"] }

add_tactic_doc
  { Name := "skip", category := DocCategory.tactic, declNames := [`tactic.interactive.skip],
    tags := ["core", "combinator"] }

add_tactic_doc
  { Name := "solve1", category := DocCategory.tactic, declNames := [`tactic.interactive.solve1],
    tags := ["core", "combinator", "goal management"] }

add_tactic_doc
  { Name := "sorry / admit", category := DocCategory.tactic,
    declNames := [`tactic.interactive.sorry, `tactic.interactive.admit],
    inheritDescriptionFrom := `tactic.interactive.sorry, tags := ["core", "testing", "debugging"] }

add_tactic_doc
  { Name := "specialize", category := DocCategory.tactic, declNames := [`tactic.interactive.specialize],
    tags := ["core", "context management", "lemma application"] }

add_tactic_doc
  { Name := "split", category := DocCategory.tactic, declNames := [`tactic.interactive.split],
    tags := ["core", "basic", "logic"] }

add_tactic_doc
  { Name := "subst", category := DocCategory.tactic, declNames := [`tactic.interactive.subst],
    tags := ["core", "rewriting"] }

add_tactic_doc
  { Name := "subst_vars", category := DocCategory.tactic, declNames := [`tactic.interactive.subst_vars],
    tags := ["core", "rewriting"] }

add_tactic_doc
  { Name := "success_if_fail", category := DocCategory.tactic, declNames := [`tactic.interactive.success_if_fail],
    tags := ["core", "testing", "combinator"] }

add_tactic_doc
  { Name := "suffices", category := DocCategory.tactic, declNames := [`tactic.interactive.suffices],
    tags := ["core", "basic", "goal management"] }

add_tactic_doc
  { Name := "symmetry", category := DocCategory.tactic, declNames := [`tactic.interactive.symmetry],
    tags := ["core", "basic", "lemma application"] }

add_tactic_doc
  { Name := "trace", category := DocCategory.tactic, declNames := [`tactic.interactive.trace],
    tags := ["core", "debugging", "testing"] }

add_tactic_doc
  { Name := "trace_simp_set", category := DocCategory.tactic, declNames := [`tactic.interactive.trace_simp_set],
    tags := ["core", "debugging", "testing"] }

add_tactic_doc
  { Name := "trace_state", category := DocCategory.tactic, declNames := [`tactic.interactive.trace_state],
    tags := ["core", "debugging", "testing"] }

add_tactic_doc
  { Name := "transitivity", category := DocCategory.tactic, declNames := [`tactic.interactive.transitivity],
    tags := ["core", "lemma application"] }

add_tactic_doc
  { Name := "trivial", category := DocCategory.tactic, declNames := [`tactic.interactive.trivial],
    tags := ["core", "finishing"] }

add_tactic_doc
  { Name := "try", category := DocCategory.tactic, declNames := [`tactic.interactive.try],
    tags := ["core", "combinator"] }

add_tactic_doc
  { Name := "type_check", category := DocCategory.tactic, declNames := [`tactic.interactive.type_check],
    tags := ["core", "debugging", "testing"] }

add_tactic_doc
  { Name := "unfold", category := DocCategory.tactic, declNames := [`tactic.interactive.unfold],
    tags := ["core", "basic", "rewriting"] }

add_tactic_doc
  { Name := "unfold1", category := DocCategory.tactic, declNames := [`tactic.interactive.unfold1],
    tags := ["core", "rewriting"] }

add_tactic_doc
  { Name := "unfold_projs", category := DocCategory.tactic, declNames := [`tactic.interactive.unfold_projs],
    tags := ["core", "rewriting"] }

add_tactic_doc
  { Name := "with_cases", category := DocCategory.tactic, declNames := [`tactic.interactive.with_cases],
    tags := ["core", "combinator"] }

/-- Navigate to the left-hand-side of a relation.
A goal of `| a = b` will turn into the goal `| a`.
-/
-- conv mode tactics
add_tactic_doc
  { Name := "conv: to_lhs", category := DocCategory.tactic, declNames := [`conv.interactive.to_lhs], tags := ["conv"] }

/-- Navigate to the right-hand-side of a relation.
A goal of `| a = b` will turn into the goal `| b`.
-/
add_tactic_doc
  { Name := "conv: to_rhs", category := DocCategory.tactic, declNames := [`conv.interactive.to_rhs], tags := ["conv"] }

/-- Navigate into every argument of the current head function.
A target of `| (a * b) * c` will turn into the two targets `| a * b` and `| c`.
-/
add_tactic_doc
  { Name := "conv: congr", category := DocCategory.tactic, declNames := [`conv.interactive.congr], tags := ["conv"] }

/-- Navigate into the contents of top-level `λ` binders.
A target of `| λ a, a + b` will turn into the target `| a + b` and introduce `a` into the local
context.
If there are multiple binders, all of them will be entered, and if there are none, this tactic is a
no-op.
-/
add_tactic_doc
  { Name := "conv: funext", category := DocCategory.tactic, declNames := [`conv.interactive.funext], tags := ["conv"] }

/-- Navigate into the first scope matching the expression.

For a target of `| ∀ c, a + (b + c) = 1`, `find (b + _) { ... }` will run the tactics within the
`{}` with a target of `| b + c`.
-/
add_tactic_doc
  { Name := "conv: find", category := DocCategory.tactic, declNames := [`conv.interactive.find], tags := ["conv"] }

/-- Navigate into the numbered scopes matching the expression.

For a target of `| λ c, 10 * c + 20 * c + 30 * c`, `for (_ * _) [1, 3] { ... }` will run the
tactics within the `{}` with first a target of `| 10 * c`, then a target of `| 30 * c`.
-/
add_tactic_doc
  { Name := "conv: for", category := DocCategory.tactic, declNames := [`conv.interactive.for], tags := ["conv"] }

/-- End conversion of the current goal. This is often what is needed when muscle memory would type
`sorry`.
-/
add_tactic_doc
  { Name := "conv: skip", category := DocCategory.tactic, declNames := [`conv.interactive.skip], tags := ["conv"] }

