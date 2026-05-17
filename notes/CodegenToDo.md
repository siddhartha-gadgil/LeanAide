# Codegen TODO for `mathdoc_agent`

This note compares the compact JSON emitted by `mathdoc_agent` with the
handlers currently available through `LeanAide/PaperCodes.lean` and
`LeanAideCore/LeanAideCore/PaperCodes.lean`.

The Python exporter should continue to emit PaperStructure-style objects with a
`type` field. Lean dispatches through `type`, so generated JSON should not use
`kind` in saved outputs.

## Currently Matched Structures

These structures are already supported by Lean codegen and are emitted with
matching field names.

### `document`

- `body`: array of document nodes.
- `title`: optional metadata, currently ignored by Lean codegen.

### `Theorem`

- `claim`: theorem statement translated by Lean.
- `hypothesis`: optional array of hypotheses.
- `proof`: optional proof object.
- `label`: optional theorem label.
- `header`, `id`, `status`: metadata, currently ignored by Lean codegen.

### `Proof`

- `proof_steps`: array of proof steps.
- `claim_label`: optional label used when generating standalone command
  sequences.

### `assert_statement`

- `claim`: asserted proposition.
- `proof_method`: optional metadata, currently ignored by Lean codegen.
- `results_used`: optional references, currently ignored by Lean codegen.
- `deduced_from_claim`: optional local/contextual claims used for the
  assertion, currently ignored by Lean codegen.
- `deduced_from_theorem`: optional standard theorem objects used for the
  assertion, currently ignored by Lean codegen.

### `calculation`

- `inline_calculation`: single calculation string, or
- `calculation_sequence`: array of calculation strings.

### `induction_proof`

- `on`: induction variable or expression.
- `prev_var`: optional previous variable name.
- `base_case_proof`: proof object for the base case.
- `induction_step_proof`: proof object for the induction step.

### `multi-condition_cases_proof`

- `proof_cases`: array of case objects.
- Each case has:
  - `condition`: case condition.
  - `proof`: proof object for that case.
- `exhaustiveness`: optional proof of case coverage. The Python exporter
  currently omits this unless it has a formal proof object; prose text here is
  not useful to Lean.

### `bi-implication_cases_proof`

- `if_proof`: forward implication proof.
- `only_if_proof`: reverse implication proof.

### `contradiction_statement`

- `assumption`: assumption to contradict.
- `proof`: proof object deriving the contradiction.

The Python exporter now emits `proof` here as a `Proof` object with
`proof_steps`, not as a raw array.

## Python Field Adjustments Already Made

- Contradiction proofs now use `proof : { type := "Proof", proof_steps := ... }`.
- Case proofs no longer emit prose-only `exhaustiveness`.
- Theorem nodes emit `claim`, not `statement`.
- Proof nodes do not repeat the theorem statement inside the proof.
- Saved JSON examples use `type`; `kind` is only used internally in Python.

## Lean Field Mismatches To Watch

### `general_induction_proof`

Lean's schema comment mentions `induction_hypotheses`, but the implementation
reads `induction_hyps` inside each case.

Recommended Lean-side fix: accept both names, with `induction_hyps` as the
current compatibility spelling.

Case fields:

- `condition`: case condition.
- `proof`: proof object.
- `induction_hyps` or `induction_hypotheses`: induction hypotheses.

#### Update: Added option

### `bi-implication_cases_proof`

The schema comment mentions `antecedent` and `consequent`, but the codegen
implementation only requires `if_proof` and `only_if_proof`.

Recommended action: keep Python as-is unless Lean codegen starts using the
extra fields.

#### Update: Nothing to do

## Dependency Field Support Needed

`mathdoc_agent` now emits structured dependency fields on logical proof steps
and calculation steps. Lean codegen should preserve and use these fields instead
of treating them as disposable metadata.

Primary fields:

- `deduced_from_claim`: array of local/contextual mathematical claims. These are
  not theorem names; they should be translated as propositions and used as
  local facts, `have` candidates, or search context.
- `deduced_from_theorem`: array of theorem objects. Each object has:
  - `claim`: general theorem statement.
  - `name`: optional theorem name.
  - `description`: optional note on how the theorem is used.
- `proof_method`: local proof hint or method label.
- `hints`, `referenced_lemmas`, `referenced_hypotheses`: optional guidance from
  coarse proof refinement.

Recommended Lean-side behavior:

- Extend `assertionCode` for `assert_statement` to read
  `deduced_from_claim` and `deduced_from_theorem` before falling back to generic
  tactic search from the translated `claim`.
- For `deduced_from_theorem`, prefer an explicit `name` when it resolves to a
  known theorem. If only `claim` is present, translate the claim and use
  `getExactTerm?`/search as with `results_used`.
- For `deduced_from_claim`, translate each claim and generate named local
  `have` facts or add them to the search context before proving the assertion.
- Keep compatibility with the older `results_used` array by either mapping it
  into the new dependency representation or by making a shared helper read all
  supported dependency fields.
- Consider tolerating the misspelling `deduce_from_theorem` as an alias for
  `deduced_from_theorem` if any saved examples contain it, but prefer emitting
  and documenting the `deduced_from_theorem` spelling.

Handlers that should share this dependency parser:

- `assert_statement`: most important target; dependencies should guide the
  generated `have` proof.
- `Proof` / generic proof-step dispatch: preserve top-level dependency fields
  when a simple proof fragment is not decomposed into separate steps.
- Specific calculation handlers such as `equality_chain`, `inequality_chain`,
  `rewrite_by_hypothesis`, and related calculation kinds: use dependency fields
  attached to each calculation step's `justification`.
- `conclude_statement`: accept the same fields when a conclusion step cites
  local claims or standard theorems.
- Future dedicated proof handlers in this note: any handler with an internal
  `proof`, `proof_of_reduction`, `verification`, or `*_proof` field should pass
  dependency metadata through to its generated subgoals.

## New `@[codegen]` Handlers Needed

The following proof types are generated or recognized by `mathdoc_agent` but
currently degrade to generic `Proof` or `assert_statement` structures when Lean
does not have a dedicated handler. Dedicated handlers would preserve proof
intent and produce better Lean tactics.

### `contrapositive_proof`

JSON type to match: `contrapositive_proof`.

Fields:

- `assumption`: negated conclusion or contrapositive assumption.
- `proof`: proof deriving the negated hypothesis.
- `conclusion`: optional final contrapositive conclusion.

Expected Lean behavior: introduce the contrapositive assumption, derive the
negated hypothesis, and close using the contrapositive form of the theorem.

### `existence_proof`

JSON type to match: `existence_proof`.

Fields:

- `claim`: required existential claim being proved.
- `witness`: constructed witness.
- `proof`: verification that the witness satisfies the predicate.

Expected Lean behavior: use the witness, then generate tactics for the
verification proof.

Use this type when the main mathematical act is proving an already stated
existential proposition, usually by providing a witness for `∃ x, P x`.

### `uniqueness_proof`

JSON type to match: `uniqueness_proof`.

Fields:

- `existence_proof`: proof that at least one object exists.
- `uniqueness_proof`: proof that any two candidates are equal.
- `candidate_variables`: optional names for arbitrary candidates.
- `claim`: optional uniqueness or `exists unique` statement.

Expected Lean behavior: split existence and uniqueness goals, then prove the
equality of arbitrary candidates.

### `construction_proof`

JSON type to match: `construction_proof`.

Fields:

- `claim`: required existential claim or target property supplied by the
  construction.
- `construction`: constructed object or definition.
- `verification`: proof that the construction has the required property.

Expected Lean behavior: define or refine the constructed object, then discharge
the verification goals.

Use this type when the proof must build a mathematical object, map, structure,
definition, or auxiliary datum that will be used as an object in the surrounding
argument. Unlike `existence_proof`, the construction itself is first-class data;
the existential claim records what property the constructed object is meant to
certify.

### `generic_element_proof`

JSON type to match: `generic_element_proof`.

Fields:

- `element`: arbitrary element introduced for the proof.
- `target_relation`: relation being proved, such as set equality or inclusion.
- `proof`: proof for the arbitrary element.
- `direction_proofs`: optional directional proofs for equality-style goals.

Expected Lean behavior: use extensionality or inclusion introduction, introduce
the generic element, and generate the elementwise proof.

### `epsilon_delta_proof`

JSON type to match: `epsilon_delta_proof`.

Fields:

- `epsilon_var`: epsilon variable name.
- `epsilon_positive`: positivity hypothesis for epsilon.
- `delta`: chosen delta expression.
- `delta_positive_proof`: proof that delta is positive.
- `bound_claim`: bound or implication to prove after the delta is chosen.
- `bound_proof`: proof of the required bound.

Expected Lean behavior: introduce epsilon and its positivity hypothesis, use
the proposed delta, prove positivity, then prove the implication/bound.

### `invariant_proof`

JSON type to match: `invariant_proof`.

Fields:

- `invariant`: invariant predicate.
- `initial_proof`: proof that the invariant holds initially.
- `preservation_proof`: proof that every step preserves the invariant.
- `conclusion`: result obtained from the invariant.

Expected Lean behavior: prove initialization and preservation, then apply the
invariant to the target state.

### `reduction_proof`

JSON type to match: `reduction_proof`.

Fields:

- `claim`: current claim being reduced.
- `reduced_to`: target result or previously proved theorem.
- `proof_of_reduction`: proof object showing that `claim` follows from, or is
  reduced to, `reduced_to`.
- `proof`: proof object for the reduced goal `reduced_to`.

Expected Lean behavior: first prove the reduction from `claim` to `reduced_to`,
then prove the reduced goal. This avoids separating "reduction steps" from
"result used"; the result/theorem being used should appear inside either
`proof_of_reduction` or `proof` as an ordinary proof reference.

### `counting_proof`

JSON type to match: `counting_proof`.

Fields:

- `counted_object`: finite type, set, or combinatorial object being counted.
- `first_count`: first counting argument.
- `second_count`: second counting argument.
- `equality_proof`: proof that the two counts are equal.

Expected Lean behavior: produce a finite-cardinality equality from two
cardinality computations.

### `pigeonhole_proof`

JSON type to match: `pigeonhole_proof`.

Fields:

- `objects`: objects being assigned.
- `boxes`: boxes or target classes.
- `assignment`: map from objects to boxes.
- `cardinality_proof`: proof that there are more objects than boxes.
- `conclusion`: collision or repeated-box conclusion.

Expected Lean behavior: apply an appropriate finite pigeonhole theorem.

### `minimal_counterexample_proof`

JSON type to match: `minimal_counterexample_proof`.

Fields:

- `counterexample_property`: property defining counterexamples.
- `minimal_element`: chosen minimal counterexample.
- `minimality_proof`: proof of minimality.
- `contradiction_proof`: proof contradicting minimality or counterexamplehood.

Expected Lean behavior: obtain a minimal counterexample by well-foundedness,
then derive a contradiction.

### `infinite_descent_proof`

JSON type to match: `infinite_descent_proof`.

Fields:

- `initial_counterexample`: starting counterexample.
- `descent_step`: construction of a smaller counterexample.
- `well_founded_relation`: relation used for descent.
- `contradiction_proof`: final contradiction from well-foundedness.

Expected Lean behavior: use well-founded descent or `Nat` minimality to rule
out the initial counterexample.

### `compactness_proof`

JSON type to match: `compactness_proof`.

Fields:

- `cover_or_family`: open cover or closed family.
- `finite_subcover_proof`: proof extracting a finite subcover/subfamily.
- `local_proof`: optional proof on finite data.
- `conclusion`: target compactness consequence.

Expected Lean behavior: apply the compactness theorem and pass to finite data.

### `density_proof`

JSON type to match: `density_proof`.

Fields:

- `dense_subset`: subset known or proved dense.
- `dense_proof`: proof of density.
- `extension_or_limit_step`: proof transferring the result by density.
- `conclusion`: target conclusion.

Expected Lean behavior: apply density or closure lemmas, then close by
continuity/order/topological transfer.

### `approximation_proof`

JSON type to match: `approximation_proof`.

Fields:

- `approximants`: approximating sequence, net, or family.
- `approximation_error`: bound or convergence statement.
- `limit_passage`: proof passing to the limit.
- `conclusion`: target result.

Expected Lean behavior: introduce approximants, prove estimates, and use a
limit theorem.

### `universal_property_proof`

JSON type to match: `universal_property_proof`.

Fields:

- `universal_property`: property being invoked.
- `existence_part`: proof constructing the comparison map/object.
- `uniqueness_part`: proof of uniqueness.
- `comparison_map`: optional explicit map.

Expected Lean behavior: use the universal property constructor or eliminator,
then prove existence and uniqueness subgoals.

### `algorithmic_proof`

JSON type to match: `algorithmic_proof`.

Fields:

- `algorithm`: algorithm or recursive procedure.
- `termination_proof`: proof of termination.
- `partial_correctness_proof`: proof that the result is correct if returned.
- `conclusion`: target correctness theorem.

Expected Lean behavior: define/refine the algorithm, prove termination, then
prove correctness.

### `probabilistic_proof`

JSON type to match: `probabilistic_proof`.

Fields:

- `probability_space`: probability space or measure context.
- `bad_event_bound`: bound on undesirable events.
- `positive_probability_proof`: proof that a good event has positive
  probability.
- `witness_conclusion`: deterministic existence conclusion.

Expected Lean behavior: prove the probability bound and extract existence from
positive probability.

### `local_to_global_proof`

JSON type to match: `local_to_global_proof`.

Fields:

- `cover`: local cover or localization data.
- `local_proofs`: proofs on each local piece.
- `compatibility_proof`: proof that local data agree on overlaps.
- `gluing_step`: construction of the global object/proof.

Expected Lean behavior: use a gluing or sheaf-style theorem after local and
compatibility goals are solved.

### `diagram_chase_proof`

JSON type to match: `diagram_chase_proof`.

Fields:

- `diagram`: named diagram or maps.
- `start_element`: element introduced at the start of the chase.
- `map_steps`: sequence of element images or preimages.
- `exactness_or_commutativity_uses`: facts used in the chase.
- `conclusion`: final element relation.

Expected Lean behavior: introduce elements, rewrite by commutativity, and use
exactness lemmas.

### `maximal_minimal_proof`

JSON type to match: `maximal_minimal_proof`.

Fields:

- `object`: extremal object.
- `ordering`: relation used for maximality/minimality.
- `extremal_property`: proof that the object is extremal.
- `improvement_contradiction`: proof that any improvement contradicts
  extremality.

Expected Lean behavior: choose an extremal object, assume an improving object,
and contradict maximality/minimality.

### `genericity_ae_proof`

JSON type to match: `genericity_ae_proof`.

Fields:

- `bad_set`: exceptional set.
- `smallness_proof`: proof the bad set is meagre/null/finite.
- `generic_condition`: condition holding outside the bad set.
- `conclusion`: almost-everywhere or generic conclusion.

Expected Lean behavior: prove smallness of the exceptional set, then apply the
corresponding almost-everywhere or genericity theorem.

### `diagrammatic_geometric_proof`

JSON type to match: `diagrammatic_geometric_proof`.

Fields:

- `configuration`: geometric objects and incidence data.
- `construction_steps`: auxiliary points, lines, or maps.
- `geometric_facts`: lemmas used in the diagrammatic argument.
- `conclusion`: target geometric statement.

Expected Lean behavior: introduce the configuration, construct auxiliaries, and
apply geometric lemmas to close the conclusion.

## Recommended Order

1. Add `contrapositive_proof`, `existence_proof`, `generic_element_proof`, and
   `epsilon_delta_proof`; these appear in the current example corpus and are
   the most useful next targets.
2. Add `uniqueness_proof`, `construction_proof`, `invariant_proof`, and
   `reduction_proof`; these are common enough to justify specialized
   generation.
3. Keep less common proof types degrading to supported core structures until
   there are examples that require more precise Lean behavior.

## Declaration Codegen Handlers Needed

`mathdoc_agent` now emits Lean-oriented declaration nodes for definitions that
are not theorem/proof objects. These should be handled as top-level document
items, producing Lean commands rather than proof scripts.

Example JSON is generated by:

```bash
./venv/bin/python -m mathdoc_agent.examples.lean_definition_examples
```

The generated fixture is:

```text
mathdoc_agent/examples/lean_definition_examples.json
```

### Shared Lean-Side Guidance

- Dispatch on the node's `type` field, just as theorem/proof codegen does.
- These handlers should return `CommandSeq`/document command output, not proof
  fragments.
- Prefer Lean Unicode in generated declarations (`α`, `→`, `≤`, etc.) because
  the Python examples now emit Lean-like strings.
- Preserve labels, ids, and status only as optional comments or trace metadata;
  they should not affect elaborated Lean code.
- Treat `parameters` as declaration binders that come before fields or
  constructors.
- Strings in fields and constructor arguments are already close to Lean syntax.
  Initially, parse them as raw syntax snippets and generate conservative code;
  later they can be passed through translator/code repair if elaboration fails.
- Useful fallback: if a declaration cannot be generated precisely, emit a
  commented block with the intended declaration and a `-- TODO` note rather than
  generating malformed Lean.

### `structure-definition`

JSON type to match: `structure-definition`.

Fields:

- `name`: Lean declaration name.
- `is_class`: whether to emit `class` instead of `structure`.
- `parameters`: optional array of binders, e.g. `["α : Type", "le : α → α → Prop"]`.
- `extends`: optional array of parent structures/classes.
- `fields`: array of field objects:
  - `name`: field name.
  - `type`: field type.
  - `default`: optional default value.
- `text`: source prose for comments or repair prompts.

Expected Lean behavior:

- If `is_class = false`, emit:

  ```lean
  structure SortedList (α : Type) (le : α → α → Prop) where
    xs : List α
    sorted : List.Pairwise le xs
  ```

- If `is_class = true`, emit:

  ```lean
  class Magma where
    carrier : Type
    mul : carrier → carrier → carrier
  ```

- If `extends` is nonempty, emit `structure Name ... extends Parent₁, Parent₂ where`
  or `class Name ... extends Parent₁, Parent₂ where`.
- If a field has `default`, emit `field_name : field_type := default`.
- For "data and property" structures, both data fields and proof/property fields
  are plain structure fields. Example: `BoundedNat` has data `n : Nat` and
  property `bound : n ≤ b`.

Implementation notes:

- Add a `@[codegen]` handler for `structure-definition`.
- Add a parser helper for optional arrays of strings (`parameters`, `extends`).
- Add a parser helper for field objects with required `type` and optional
  `name`/`default`.
- The field name should be required for generated Lean. If omitted, either infer
  a stable name such as `field1` or emit a TODO comment.

### `instance-definition`

JSON type to match: `instance-definition`.

Fields:

- `name`: optional instance declaration name.
- `class_name`: class being instantiated.
- `target`: target type or target expression.
- `parameters`: optional array of binders.
- `fields`: object mapping field names to implementation expressions.
- `value`: optional raw instance expression or prose summary.
- `text`: source prose for comments or repair prompts.

Expected Lean behavior:

- If `fields` is present, emit a structure-style instance body:

  ```lean
  instance natAddMagma : Magma where
    carrier := Nat
    mul := Nat.add
  ```

- If `class_name` and `target` should be combined into an applied class, emit
  `: ClassName Target` only when the class expects a target argument. For the
  current `Magma` example, the target is metadata and `: Magma` is enough because
  `carrier` is a field.
- If `value` is a usable Lean expression and `fields` is absent, emit:

  ```lean
  instance name : ClassName Target := value
  ```

- If `name` is absent, emit an anonymous instance:

  ```lean
  instance : ClassName Target where
    ...
  ```

Implementation notes:

- Add a `@[codegen]` handler for `instance-definition`.
- Be conservative about the instance type: classes vary between bundled
  structures (`Magma`) and typeclass-on-carrier shapes (`Group G`). If both
  `class_name` and `target` are present, a first heuristic is:
  - if `fields` contains `carrier`, use `: class_name`;
  - otherwise use `: class_name target`.
- Long term, add a repair pass that tries both instance signatures when Lean
  elaboration fails.

### `inductive-type-definition`

JSON type to match: `inductive-type-definition`.

Fields:

- `name`: Lean inductive declaration name.
- `is_prop`: whether the inductive family lives in `Prop`; otherwise emit a
  normal `Type` inductive.
- `parameters`: optional array of declaration binders.
- `constructors`: array of constructor objects:
  - `name`: constructor name.
  - `arguments`: array of named typed arguments, e.g.
    `["n : Nat", "h : Even n"]`.
- `text`: source prose for comments or repair prompts.

Expected Lean behavior:

- For propositions, emit an inductive proposition:

  ```lean
  inductive Even : Nat → Prop where
    | zero_even : Even 0
    | step_even (n : Nat) (h : Even n) : Even (n + 2)
  ```

- For types, emit an inductive type:

  ```lean
  inductive BinaryTree (α : Type) : Type where
    | leaf : BinaryTree α
    | node (left : BinaryTree α) (label : α) (right : BinaryTree α) : BinaryTree α
  ```

Important limitation:

- The current JSON schema records constructor arguments but not constructor
  result targets. For many inductive families, especially propositions such as
  `Even : Nat → Prop`, the target of each constructor is essential:
  `zero_even : Even 0`, `step_even ... : Even (n + 2)`.
- Recommended Lean-side fallback for now: use `text` plus constructor arguments
  to prompt/repair the full declaration, or emit a commented TODO if targets
  cannot be inferred.
- Recommended Python/schema improvement: add optional constructor field
  `target` or `result` so the JSON can explicitly contain:
  - `{"name": "zero_even", "arguments": [], "target": "Even 0"}`
  - `{"name": "step_even", "arguments": ["n : Nat", "h : Even n"], "target": "Even (n + 2)"}`

Implementation notes:

- Add a `@[codegen]` handler for `inductive-type-definition`.
- Add a constructor parser for `name`, `arguments`, and, after the schema
  improvement, `target`.
- For `is_prop = true`, the declaration result should usually be `... → Prop`.
  Without an explicit family type/result target, this cannot be reliably derived
  from constructor arguments alone.
- For `is_prop = false`, default to `: Type` when no result universe is
  specified.

### Suggested Declaration Handler Order

1. Add `structure-definition`, since fields and parameters are already enough
   for valid Lean in the current examples.
2. Add `instance-definition`, initially with the conservative bundled-structure
   heuristic and repair fallback.
3. Extend the Python constructor schema with optional constructor targets.
4. Add `inductive-type-definition` after target/result data is available, or
   implement a prompt-backed fallback for examples where targets must be
   inferred from prose.

## Calculation Codegen Handlers Needed

`mathdoc_agent` now resolves core `calculation_kind` values to specific JSON
`type`s when exporting calculations. Unknown calculation kinds still fall back
to the older generic `calculation` object with `calculation_sequence` or
`inline_calculation`.

The common core calculation shape is:

```json
{
  "type": "equality_chain",
  "start": "A",
  "target": "B",
  "goal_relation": "=",
  "steps": [
    {
      "from": "A",
      "relation": "=",
      "to": "A₁",
      "justification": "lemma or local reason",
      "side_conditions": []
    }
  ]
}
```

Shared Lean-side guidance:

- Add `@[codegen]` handlers dispatching on these calculation `type` values.
- Treat `steps` as the primary source of the Lean `calc` block.
- `from`, `relation`, and `to` are intended as Lean-adjacent expressions.
- `justification` is prose or a lemma name; first implementation can turn it
  into `by aesop?`, `by simpa [...]`, `by ring`, `by nlinarith`, etc., depending
  on the handler.
- `side_conditions` should become subgoals, local `have` statements, or comments
  for a repair pass.
- If a specialized handler fails, fall back to the generic `calculation` handler
  and preserve the original step data in comments.

### `equality_chain`

Fields: common calculation fields.

Expected Lean behavior: emit a `calc` block whose relations are all equality,
using each step justification for the corresponding `:= by ...` proof.

Likely tactics: `simpa`, `rw`, `ring`, `simp`, or repair-guided theorem search.

### `inequality_chain`

Fields: common calculation fields.

Expected Lean behavior: emit a `calc` block with `<`, `≤`, `>`, or `≥` steps.
Each step may require an order lemma or arithmetic tactic.

Likely tactics: `linarith`, `nlinarith`, `positivity`, monotonicity lemmas, or
explicit named inequalities.

### `mixed_relation_chain`

Fields: common calculation fields.

Expected Lean behavior: emit a heterogeneous `calc` block when Lean accepts the
relation transitions, otherwise split the chain into smaller assertions.

Likely tactics: relation transitivity lemmas, `calc`, `linarith`, and explicit
coercion/cast normalization.

### `rewrite_by_hypothesis`

Fields: common calculation fields. `justification` should name or describe the
hypothesis when possible.

Expected Lean behavior: use `rw [h]`, `rw [← h]`, or `simpa [h]` at the target
expression.

### `rewrite_by_lemma`

Fields: common calculation fields. `justification` should name or describe the
lemma when possible.

Expected Lean behavior: use `rw [lemma]`, `simpa [lemma]`, or theorem search to
identify a rewrite lemma.

### `definition_unfolding`

Fields: common calculation fields.

Expected Lean behavior: unfold definitions used in the step and simplify.

Likely tactics: `simp [definition_name]`, `unfold definition_name`, or
`change ...`.

### `normalization`

Fields: common calculation fields.

Expected Lean behavior: normalize both sides of a calculation step to a common
form.

Likely tactics: `ring`, `ring_nf`, `norm_num`, `simp`, `omega`, `linarith`,
or `nlinarith`, selected by expression class.

### `positivity_side_goal`

Fields: common calculation fields plus `side_conditions`.

Expected Lean behavior: prove positivity/nonnegativity side goals needed by a
main calculation step.

Likely tactics: `positivity`, `nlinarith`, `linarith`, `norm_num`.

### `monotonicity_step`

Fields: common calculation fields.

Expected Lean behavior: apply monotonicity of a function/operator to a previous
inequality.

Likely tactics: `gcongr`, monotonicity lemmas, or explicit application of
`Monotone`/`StrictMono` hypotheses.

### `triangle_inequality_estimate`

Fields: common calculation fields.

Expected Lean behavior: introduce an intermediate norm/absolute-value estimate
using triangle inequality and then simplify/bound terms.

Likely tactics: `calc`, `nlinarith`, `linarith`, `simpa` using norm or absolute
value lemmas.

### `add_subtract_intermediate`

Fields: common calculation fields.

Expected Lean behavior: insert and subtract an intermediate term, then split an
estimate, often before triangle inequality.

Likely tactics: `ring_nf` for algebraic rearrangement, then inequality tactics.

### `casewise_calculation`

Fields: common calculation fields. In future, this may need explicit cases.

Expected Lean behavior: split into cases before running the calculation in each
case. For now, if only `steps` are present, emit a normal calculation and leave
case information to surrounding proof nodes.

Likely tactics: `by_cases`, `rcases`, `split`, `simp` in each branch.

### `inductive_step_calculation`

Fields: common calculation fields.

Expected Lean behavior: use induction hypotheses and recursive/inductive
definitions to prove the step calculation.

Likely tactics: `simp` with recursive definitions and induction hypotheses,
then `ring`, `omega`, or `linarith`.

### `extensionality_then_pointwise_calculation`

Fields: common calculation fields.

Expected Lean behavior: first apply extensionality (`ext x`, `funext x`, set
extensionality, component extensionality), then use a pointwise calculation.

Likely tactics: `ext`, `funext`, `constructor`, followed by `simp`, `calc`, or
the chain handler.

### `calculation_to_contradiction`

Fields: common calculation fields.

Expected Lean behavior: derive an impossible final relation such as `n < n`,
`0 < 0`, or `1 = 0`, then close the contradiction.

Likely tactics: `exact absurd ...`, `linarith`, `omega`, `norm_num`, or
irreflexivity/nonzero lemmas.

### Suggested Calculation Handler Order

1. Implement `equality_chain`, `rewrite_by_hypothesis`, `rewrite_by_lemma`,
   `definition_unfolding`, and `normalization`; these cover basic algebraic
   calculations and are easiest to lower to Lean.
2. Add `inequality_chain`, `mixed_relation_chain`, `positivity_side_goal`, and
   `monotonicity_step`; these cover most order/arithmetic calculations.
3. Add estimate and structural handlers:
   `triangle_inequality_estimate`, `add_subtract_intermediate`,
   `casewise_calculation`, `inductive_step_calculation`,
   `extensionality_then_pointwise_calculation`, and
   `calculation_to_contradiction`.
