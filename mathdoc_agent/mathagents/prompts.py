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
Avoid local-definition syntax inside theorem statements, especially phrases
such as `if C_n := ... then ...`. Instead state the local definition as a named
function or object in mathematical prose: for example, "Let C : Nat -> G be
defined by C n = ... . For every n, ... C n ...". Use ASCII identifier-style
names such as `C`, `normQ`, `barL`, `VQ`, `twoN`, and `sumSigns` in statements
when the source notation is display-heavy.
If a proof immediately follows a theorem-like statement, attach the proof text
to thdefinitionsm-like child in `proof_text`. Do not emit the proof as a separate
paragraph. A text beginning with "Proof." or "Proof:" is never a paragraph.
For ordinary definition children, fill Lean-codegen metadata through
`data_entries`: use key `term` for a short ASCII Lean-style identifier or
declaration name such as `PseudoLength`, `IsLength`, `IsHomogeneousPseudoLength`,
`commutator`, `commutatorSubgroup`, `abelianization`, or `torsionSubgroup`; use
key `definiens` for only the mathematical definition, without Markdown headers,
bold markers, numbering labels, or explanatory prose. Use key `notation` only
when the source explicitly defines notation. Never use prose names containing
spaces, hyphens, parentheses, LaTeX, or display math as the definition `term`.
For structure-definition children, set `name`, `is_class`, `isProp`,
parameters, extends, and fields. Use `is_class=true` for class-like structures
such as groups. Parameters must be objects with `name`, `type`, and optional
`binder`; `binder` is one of `default`, `implicit`, or `typeclass`, and defaults
to `default` when omitted.
For instance-definition children, set `class_name`, `target`, optional `name`,
parameters, `gives`, and value when present. `gives` is an array of objects with
`name` and `value`.
For inductive-type-definition children, set `name`, `is_prop`, parameters,
indices, and constructors. Parameters and indices use the same `name`, `type`,
`binder` object shape as structure parameters. Each constructor should include
its name, when stated, and its arguments.
Use `data_entries` only for small string metadata as key/value pairs.
Prefer labels that are stable source labels such as `Lemma 1`, `Proposition 7`,
or a short ASCII identifier. Avoid putting full claims or display notation in
labels.
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
If the fragment primarily instantiates an already-proved universal or
implicational claim at particular local values or hypotheses, classify it as
kind='specialize'. This proof kind is exported as an additional named `have`
for the specialized instance; it must not overwrite or forget the original
general claim and must not be represented as Lean's destructive `specialize`
tactic.
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

SPECIALIZE_INSTRUCTIONS = """
Refine a proof fragment whose purpose is to instantiate an already-proved
claim, theorem, or hypothesis at particular local values or hypotheses.
Return a new named local lemma for the specialized instance. The downstream
JSON will be an additional `assert_statement`/`have`, not Lean's destructive
`specialize h ...` tactic, because the original general claim must remain
available.

Fill:
- `name`: a Lean-style ASCII identifier for the new specialized lemma.
- `lean_term`: the exact Lean term proving the specialized lemma, possibly
  depending on local variables and hypotheses, such as `(h x hx)` or
  `(Nat.succ_le_succ hnm)`.
- `claim`: the mathematical statement of the specialized lemma when clear.
- `source_claim`: the general already-proved claim being instantiated when
  clear.
- `arguments`: the local values or hypotheses used for the specialization.

Do not invent a `lean_term` if the local Lean names are not available; leave an
unresolved detail instead.
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
Use Lean-codegen-friendly names in `let_statement.variable_name`: ASCII
identifier-style names such as `normQ`, `basisNorm`, `iota`, `eps`, `twoN`,
`comm`, or `quotientMap`. Do not use display names such as `||·||_Q`,
`(B, iota)`, subscripts, Greek letters, comma-separated tuples, or LaTeX as a
variable name; if the source constructs several objects, split them into
separate `let_statement` steps with one identifier each.
Whenever an `assert_statement` has a `proof_method`, also fill dependency
fields when the source supports them:
- `deduced_from_claim`: local/contextual claims used for the assertion, stated
  as mathematical assertions. Use this for hypotheses or earlier derived
  claims that are being specialized, rewritten, combined, or slightly restated
  rather than copied verbatim from the immediate context.
- `deduced_from_theorem`: standard theorem objects used for the assertion. Each
  object must have a `claim` field giving the general theorem, and may have
  `name`, `description`, `lean_name`, and `lean_term` fields. Use `lean_name`
  only for an exact Lean/Mathlib declaration name found by LeanSearch; do not
  invent Lean names. If the theorem is used after instantiating it at particular
  local values or hypotheses, add `lean_term` with the exact Lean expression for
  that instance, such as `(Nat.succ_le_succ hnm)` or `(le_trans hxy hyz)`. Omit
  `lean_term` when the specific instantiated term is not clear.
Do not put method names, tactic names, or bare labels in `deduced_from_claim`.
For example, do not write `Second derivative test` as a claim dependency; use
`deduced_from_theorem` with a theorem object whose `claim` states the test and
whose `lean_name` is filled only when a LeanSearch match is available; include
`lean_term` only when the instantiated Lean proof term is clear.
When an assertion depends on a previously labeled theorem or lemma from the
same document, mention that label in `proof_method` or in the theorem object's
`name`; keep the `claim` itself as the mathematical proposition being proved.
If the fragment is represented as one simple proof with `method` rather than
separate `proof_steps`, use the top-level `deduced_from_claim` and
`deduced_from_theorem` fields by the same rules.
Every `assert_statement.claim` must be the mathematical assertion being proved,
not an instruction. For example use `B(x, ε/3) ∩ B(y, ε/3) ≠ ∅`,
`z ∈ B(x, ε/3) ∩ B(y, ε/3)`, or
`B(x, ε/3) ∩ B(y, ε/3) = ∅`, not "negate the desired conclusion",
"produce a witness", "verify the witness", or "conclude the claim".
Keep claims close to Lean-codegen prose. Prefer local ASCII names already
introduced in the proof over raw display notation: use `barL` instead of
`\\bar l`, `normQ` instead of `‖·‖_ℚ` or `||·||_Q`, `VQ` instead of
`V_ℚ`, `twoN` instead of subscripted `2n` notation when it is an object name,
and `expectation`/`finite average` prose instead of `𝔼` when possible.
Before emitting an assertion, check that every local object named in the claim
has actually been introduced in the available proof context. If a previous step
only proves an existential statement, do not refer to its witnesses by names
such as `q_1`, `r`, `M_n`, or `K_n` unless the proof explicitly destructures the
existential or introduces those names with a `let_statement`/witness step.
When the source uses probabilistic shorthand, do not invent expectation,
random-variable, or stochastic-process assertions unless the probability space,
distribution, and process variables have been introduced. Prefer the exact
deterministic finite-average or two-case inequality stated in the source; if
the formal stochastic setup is missing, record it as an unresolved detail.
In noncommutative algebra, preserve the exact order and parentheses supplied by
the source. Do not replace a recurrence or product expression by a more
convenient one unless it follows by associativity alone or an explicit
commutation/conjugation hypothesis is available.
Do not expand omitted arguments, but do keep all intermediate equations and
algebraic rewrites that are present in the source text.
Avoid extracting obvious typing side conditions as standalone assertions, for
example `x ∈ G`, `s^{-1} ∈ G`, `n > 0`, or "`l` is a pseudo-length function",
when they are already hypotheses or fixed-variable context. Keep them in
assumptions, variable types, or proof methods instead.
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
  may have `name`, `description`, `lean_name`, and `lean_term` fields. For
  example, do not put "Second derivative test" by itself in a dependency list;
  use an object such as `{name: "second derivative test", claim: "If f''(x) > 0
  on an interval, then f is strictly convex on that interval"}`. Use `lean_name`
  only for an exact Lean/Mathlib declaration name found by LeanSearch; do not
  invent Lean names. If the step uses a theorem instantiated at particular
  local values or hypotheses, add `lean_term` with the exact Lean expression for
  that instance, such as `(Nat.succ_le_succ hnm)` or `(le_trans hxy hyz)`. Omit
  `lean_term` when the specific instantiated term is not clear.
Do not put method names, tactic names, or bare labels in `deduced_from_claim`.
Keep local hypotheses out of `deduced_from_theorem`; reserve that field for
standard mathematical results.
Before emitting a calculation step, check that all variables and indexed
families appearing in `lhs` and `rhs` are in scope. If the calculation uses
witnesses extracted from an existential statement, add or preserve the witness
introduction step first. For noncommutative products, only use associativity
for regrouping; never commute factors or change the order of multiplication
unless the source explicitly supplies the needed commutation fact.
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
- existence: full existential claim, variable name, witness, and verification
  that the witness satisfies the predicate;
- construction: full existential claim, variable name, constructed
  object/definition, and verification of the constructed object's required
  properties;
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
For existence and construction proofs, put the full existential proposition in
`full_claim`, put the constructed or witnessed variable name in `variable_name`,
and put only the property of that variable in `claim`. For example, for "there
exists a nonzero polynomial p such that p(a)=0", use `variable_name="p"` and
`claim="p is a nonzero polynomial such that p(a)=0"`. For epsilon-delta proofs,
fill `bound_claim` with the inequality or implication proved after choosing
delta.
For existence and construction proofs, `variable_name` must be a single
Lean-style ASCII identifier, not mathematical display notation. Use names such
as `normQ`, `subspaceN`, `quotientW`, `completionB`, `iota`, `basis`,
`basisNorm`, `linearMapPhi`, or `lengthFromNorm`. If the source constructs a
pair or tuple such as `(B, iota)`, choose a single identifier for the existential
witness only when the existential really binds one object; otherwise expose the
separate objects as child `let_statement` steps and verify the final object.
The `construction` field should be a first-class object description or
definition for that one identifier, not a paragraph of proof. Put auxiliary
definitions such as `N`, `W`, `B`, and `iota` in child proof steps.
When possible, write `construction` as an assignment-shaped phrase beginning
with the variable name, such as `normQ(v) := ...`, `completionB := ...`, or
`iota := ...`. Do not use pair notation, display norm symbols, or several
comma-separated constructions in the same `construction` field.
For generic-element proofs, do not create child proof specs whose kind is again
`generic_element`. The arbitrary element setup is the current proof node. Put
the fixed variable or membership assumption in `assumptions`, then make the
remaining child components `simple`, `calculation`, `theorem_application`,
`existence`, `cases`, or `contradiction` as appropriate. If the source only says
"take an arbitrary u" or "fix u" and gives no separate subproof, record that in
`assumptions` and do not create a child component for the setup.

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

PROOF_RESOLUTION_INSTRUCTIONS = """
Resolve one already-refined proof node into simpler proof structures for Lean
code generation.

The input proof has already been classified and refined by the ordinary proof
agents. Do not reclassify it, and do not discard its original mathematical
content. Your task is only to express the same proof using simpler structures
that already have Lean codegen handlers: `logical_sequence`, `simple`,
`calculation`, `cases`, `induction`, `contradiction`, `equivalence`,
`existence`, `uniqueness`, `construction`, `reduction`, `epsilon_delta`, and
`local_claim`.

Prefer a `logical_sequence`-style output:
- use `proof_steps` for short linear arguments;
- use `components` when the proof naturally has several named subproofs;
- each component kind should be one of the supported simpler kinds;
- use `simple` for a local assertion, `calculation` for explicit algebra or
  inequality chains, `specialize` only as a named `have` for an instance of an
  already-proved universal or implicational claim, and `cases` or `induction`
  only when those
  structures are explicitly present.
Never resolve a proof by wrapping it in a component with the same kind and same
goal as the input. In particular, do not create recursive `generic_element`
setup components such as `fix u`, `arbitrary u`, or `setup arbitrary u`; express
those setup phrases as `assume_statement` or `let_statement` proof steps, then
continue with the actual mathematical claim.

Preserve the original proof's claim, assumptions, conclusions, and named
intermediate claims. Do not invent omitted mathematics. If a specialized method
such as pigeonhole, compactness, density, approximation, diagram chase,
probabilistic method, or universal property is used, expose the actual local
claims it contributes as assert statements and put the method/theorem name in
`proof_method` or dependency fields.

Every `assert_statement.claim` must be a mathematical proposition, not an
instruction such as "apply compactness", "finish by pigeonhole", or "resolve
the diagram chase".
Do not turn nested local reasoning into theorem-like child nodes unless the
source explicitly names a reusable local claim. Prefer `assert_statement` for
ordinary intermediate facts so the surrounding proof context is preserved.
Do not introduce helper assertions whose variables are not already in the local
context. If a proof uses an unnamed witness from an existential claim, make the
witness introduction explicit before later assertions use that witness. If a
method relies on substantial omitted setup, such as a probability space,
random walk, Hamel basis coordinates, quotient/completion construction, or
noncommutative product recurrence, expose only the stated local facts and mark
the missing setup as unresolved rather than inventing a formal assertion.
"""

CLAIM_AUDIT_INSTRUCTIONS = """
Audit generated PaperStructure JSON before it is sent to Lean code generation.
The Lean side uses CodegenCore dispatch and the handlers in PaperCodes.lean.
Every JSON field named `claim` must contain only a mathematical proposition
suitable for a Lean theorem statement or `have` statement after natural-language
translation. A valid claim may mention fixed variables and hypotheses, but it
must not contain proof instructions, proof methods, reader tasks, tactic-like
phrasing, or a sequence of several proof steps.
Prefer claims phrased with local identifier names over raw display notation.
Repair claims that consist only of side conditions already present in context,
method labels, or type-membership bookkeeping by replacing them with the actual
mathematical conclusion when the container text supplies it; otherwise leave a
note rather than inventing content.
Patch proposition-shaped claims that still use LaTeX command names or display
symbols when the same object has an identifier in nearby context: replace
`\\bar l` by `barL`, `\\tilde l` by `tildeL`, `V_{\\mathbb Q}` or `V_ℚ` by `VQ`,
`||·||_Q` or `‖·‖_ℚ` by `normQ`, and probability display notation such as
`\\mathbb E` or `𝔼` by "the expectation" or "the finite average". Preserve the
same mathematical proposition; only change notation and wording.

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
- A dependency theorem object may have `claim`, `name`, `description`,
  `lean_name`, and `lean_term` fields. The `claim` field must be the general
  theorem statement, not a theorem name. Use `lean_name` only for an exact
  Lean/Mathlib declaration name found by LeanSearch; do not invent Lean names.
  Use `lean_term` only for the exact Lean expression of a theorem instance used
  in the proof, possibly depending on local variables or hypotheses.

Preserve mathematical meaning and do not invent stronger results. If there is
not enough mathematical content to form a proposition, leave the entry
unpatched and add a note explaining the issue.
"""

DEDUCED_FROM_CLAIM_REWRITE_INSTRUCTIONS = """
Rewrite generated PaperStructure JSON entries that contain `deduced_from_claim`
so they correspond to Lean proof structure.

For each dependency entry:
- If a dependency claim is already present verbatim in the available hypotheses
  or local context, omit it from `deduced_from_claim`; it is already available.
- If a dependency claim is available only through instantiating a general claim,
  theorem, or hypothesis at particular local values or hypotheses, insert a
  named `have` step immediately before the current object. The inserted step
  must be an `assert_statement` for the specialized lemma, must have `name` and
  `lean_term`, and must not overwrite or forget the original general claim.
  Fill `name` with the new lemma name and `lean_term` with the Lean term for
  the instance, such as `(h x hx)`.
- If a dependency claim is not yet available and must be proved before use,
  insert a separate named local theorem immediately before the current object.
  Give it a `name`, a proposition-shaped `claim`, and proof steps. Do not leave
  it inside `deduced_from_claim`.

Return only structured patches. Do not invent Lean terms or local names when the
context does not support them; leave the dependency unchanged instead.
"""

PROOF_SANITY_AUDIT_INSTRUCTIONS = """
Audit generated proof-step assertions before Lean code generation.

You are given a bounded list of assertion entries that deterministic checks
consider risky. For each entry, decide whether the claim is mathematically safe
as an intermediate assertion in its local context.

Flag only real risks:
- the assertion is stronger than what the source text or dependencies justify;
- the assertion quantifies over new arbitrary variables not in local context;
- the assertion has a simple counterexample as stated;
- the assertion uses informal local notation that cannot be scoped, such as
  subscripted pseudo-variables, display-only function calls, or unbound local
  abbreviations;
- the assertion turns a local definition or side condition into a universal
  theorem.

Do not object merely because a proof is hard. Do not invent missing mathematics.
If a claim is clean, return no patch for it.

When a risk is present:
- use `mark_needs_review` when the right fix is unclear. Give a concrete reason
  and a short suggested repair;
- use `replace_claim` only when the intended weaker/local claim is obvious from
  the supplied context;
- use `replace_assertion_with_steps` only when the assertion clearly bundles
  several smaller mathematical claims and those smaller claims are present in
  the context.

The goal is to prevent false or over-generalized helper claims from being sent
to Lean as if they were valid proof obligations.
"""
