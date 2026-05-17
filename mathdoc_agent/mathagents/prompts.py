"""Prompt templates for math-document parsing and proof refinement agents."""

DOCUMENT_PARSER_INSTRUCTIONS = """
Decompose mathematical document text into a structured document tree.
Preserve the author's structure and do not invent mathematical content.
Classify sections, definitions, structure-definition items, instance-definition
items, inductive-type-definition items, theorem-like statements, proofs,
remarks, examples, and paragraphs. If unsure, use kind='unknown' and add a note.
Use kind='paragraph' only for genuinely non-mathematical prose, such as
motivation, exposition, history, transitions, or commentary that makes no
mathematical assertion and introduces no mathematical object. Any paragraph
containing mathematical content must be classified as a mathematical node:
definition, structure-definition, instance-definition,
inductive-type-definition, theorem/lemma/proposition/corollary/local_claim,
calculation_block, proof, example, remark, or unknown. Do not put mathematical
definitions, claims, constructions, hypotheses, examples, equations, or
properties in JSON type "paragraph".
For theorem-like children, put the mathematical claim in the `statement` field.
The `statement` field must be a mathematical assertion, not an instruction to
the reader or prover. Do not write imperative/task text such as "show that",
"prove", "conclude", "negate the desired conclusion", or "produce a witness"
as a statement.
If a proof immediately follows a theorem-like statement, attach the proof text
to that theorem-like child in `proof_text`. Do not emit the proof as a separate
paragraph. A text beginning with "Proof." or "Proof:" is never a paragraph.
For structure-definition children, set `name`, `is_class`, parameters, extends,
and fields. Use `is_class=true` for class-like structures such as groups.
For instance-definition children, set `class_name`, `target`, optional `name`,
parameters, fields, and value when present.
For inductive-type-definition children, set `name`, `is_prop`, parameters, and
constructors. Each constructor should include its name, when stated, and its
arguments.
Use `data_entries` only for small string metadata as key/value pairs.
"""

PROOF_CLASSIFIER_INSTRUCTIONS = """
Classify one proof fragment by its outermost proof structure.
Do not deeply refine the proof.

Avoid `unknown` unless the text is not a mathematical proof fragment at all.
Avoid labels such as `direct`, `direct proof`, or `unknown proof`; they do not
have useful downstream handlers. If the proof is a direct argument, a sequence
of deductions, or otherwise does not clearly match a specialized proof family,
classify it as kind='logical_sequence'. The logical-sequence handler will split
the proof into many explicit steps and refine those steps further.
"""

INDUCTION_INSTRUCTIONS = """
Refine one induction proof fragment. Extract the induction variable, principle,
induction hypotheses, base cases, step cases, and child proof fragments.
Do not deeply refine child proofs or invent missing arguments.
"""

CASES_INSTRUCTIONS = """
Refine one case split proof fragment. Extract what is split on, the cases, case
assumptions, and an exhaustiveness reason when stated. Do not invent missing cases.
"""

SIMPLE_PROOF_INSTRUCTIONS = """
Refine a simple proof fragment by extracting method, hints, referenced lemmas,
referenced hypotheses, intermediate proof steps, and unresolved details. Do not
collapse a multi-sentence proof into a single assertion. Preserve each explicit
mathematical step as a `proof_steps` entry:
- use `let_statement` for introduced objects;
- use `assume_statement` for fixed arbitrary variables or assumptions;
- use `assert_statement` for equations, inequalities, derived claims, and final
  conclusions, with `proof_method` explaining the local justification.
Whenever an `assert_statement` has a `proof_method`, also fill dependency
fields when the source supports them:
- `deduced_from_claim`: local/contextual claims used for the assertion, stated
  as mathematical assertions. Use this for hypotheses or earlier derived
  claims that are being specialized, rewritten, combined, or slightly restated
  rather than copied verbatim from the immediate context.
- `deduced_from_theorem`: standard theorem objects used for the assertion. Each
  object must have a `claim` field giving the general theorem, and may have
  `name` and `description` fields.
Do not put method names, tactic names, or bare labels in `deduced_from_claim`.
For example, do not write `Second derivative test` as a claim dependency; use
`deduced_from_theorem` with a theorem object whose `claim` states the test.
If the fragment is represented as one simple proof with `method` rather than
separate `proof_steps`, use the top-level `deduced_from_claim` and
`deduced_from_theorem` fields by the same rules.
Every `assert_statement.claim` must be the mathematical assertion being proved,
not an instruction. For example use `B(x, ε/3) ∩ B(y, ε/3) ≠ ∅`,
`z ∈ B(x, ε/3) ∩ B(y, ε/3)`, or
`B(x, ε/3) ∩ B(y, ε/3) = ∅`, not "negate the desired conclusion",
"produce a witness", "verify the witness", or "conclude the claim".
Do not expand omitted arguments, but do keep all intermediate equations and
algebraic rewrites that are present in the source text.
"""

CALCULATION_INSTRUCTIONS = """
Refine a calculational proof fragment into calculation steps with lhs, relation,
rhs, justification, and side conditions. Do not invent omitted steps.
Whenever a step has a `justification`, also fill dependency fields when the
source supports them:
- `deduced_from_claim`: local/contextual claims used for the step, stated as
  mathematical assertions. Use this for hypotheses or earlier derived claims
  that are being specialized, rewritten, combined, or slightly restated rather
  than copied verbatim from the immediate context.
- `deduced_from_theorem`: standard theorem objects used for the step. Each
  object must have a `claim` field giving the general mathematical theorem, and
  may have `name` and `description` fields. For example, do not put "Second
  derivative test" by itself in a dependency list; use an object such as
  `{name: "second derivative test", claim: "If f''(x) > 0 on an interval, then
  f is strictly convex on that interval"}`.
Do not put method names, tactic names, or bare labels in `deduced_from_claim`.
Keep local hypotheses out of `deduced_from_theorem`; reserve that field for
standard mathematical results.
Use the most specific `calculation_kind` when the source supports it. Core
calculation kinds are:
equality_chain, inequality_chain, mixed_relation_chain, rewrite_by_hypothesis,
rewrite_by_lemma, definition_unfolding, normalization, positivity_side_goal,
monotonicity_step, triangle_inequality_estimate, add_subtract_intermediate,
casewise_calculation, inductive_step_calculation,
extensionality_then_pointwise_calculation, calculation_to_contradiction.
"""

STRUCTURED_PROOF_INSTRUCTIONS = """
Refine one proof fragment whose proof kind is supplied in the input.

Extract only the main logical components needed by that proof kind. Examples:
- contradiction: negated assumption and derivation of contradiction;
- contrapositive: assumption of the negated conclusion and proof of negated hypothesis;
- existence: existential claim, witness, and verification that the witness
  satisfies the predicate;
- construction: existential claim, constructed object/definition, and
  verification of the constructed object's required properties;
- uniqueness: existence part and uniqueness part;
- equivalence: one child per implication direction;
- reduction: current claim, reduced goal, proof of the reduction, and proof of
  the reduced goal;
- invariant: invariant definition, preservation proof, contradiction/conclusion;
- epsilon-delta: epsilon variable/positivity, delta choice, bound claim, and
  verification of that bound;
- generic element: arbitrary element setup and inclusion/member proof.

Do not deeply refine child proofs. Use child proof specs for components and mark
unresolved details when the source omits essential information. Use `metadata`
only for small string metadata as key/value pairs.
For existence and construction proofs, always fill `claim` with the existential
claim being proved, even if it repeats the theorem statement. For
epsilon-delta proofs, fill `bound_claim` with the inequality or implication
proved after choosing delta.

For every child proof spec, `goal` must be a clean mathematical proposition,
never a task description. Avoid imperative phrases such as "negate the desired
conclusion", "produce a witness", "verify the construction", or "conclude the
result". If the source only gives a task description, put that wording in
`notes` and either omit `goal` or replace it with the actual mathematical
claim, such as a nonempty-intersection assumption, an existential statement, a
membership assertion, an equality, an inequality, or the final theorem claim.
When a child proof has its own nontrivial subproof, its `goal` should be the
local claim proved by that subproof. Do not create chains of child proof specs
with the same `goal`; merge duplicate wrappers so each local claim appears once
with its proof steps.
"""

CLAIM_AUDIT_INSTRUCTIONS = """
Audit generated PaperStructure JSON before it is sent to Lean code generation.
The Lean side uses CodegenCore dispatch and the handlers in PaperCodes.lean.
Every JSON field named `claim` must contain only a mathematical proposition
suitable for a Lean theorem statement or `have` statement after natural-language
translation. A valid claim may mention fixed variables and hypotheses, but it
must not contain proof instructions, proof methods, reader tasks, tactic-like
phrasing, or a sequence of several proof steps.

For each supplied claim entry, decide whether the claim is already suitable for
Lean proposition translation. Return patches only for entries that need repair.
Do not patch claims that are already clean propositions.

When repairing:
- Use `replace_claim` when the problem is wording only. The replacement must be
  a proposition, not a command. For example use `B(x, ε/3) ∩ B(y, ε/3) = ∅`,
  not `conclude disjointness`.
- Use `replace_assertion_with_steps` only when the enclosing object is an
  `assert_statement` and the claim contains multiple mathematical assertions,
  a proof sketch, or an imperative such as "choose", "show", "prove",
  "verify", "negate", "derive", or "conclude". The replacement proof steps
  must be smaller `assert_statement`, `assume_statement`, or `let_statement`
  objects whose own `claim` fields are clean propositions.
- If a claim says that a result follows by a named method, put the result as the
  claim and put the method in `proof_method`; do not put the method in `claim`.
- A dependency theorem object may have a `claim` field, but that field must be
  the general theorem statement, not a theorem name.

Preserve mathematical meaning and do not invent stronger results. If there is
not enough mathematical content to form a proposition, leave the entry
unpatched and add a note explaining the issue.
"""
