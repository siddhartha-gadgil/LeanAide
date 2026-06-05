# mathdoc_agent Agents

This file documents the LLM-backed agents and agent-like LLM components used by
`mathdoc_agent`. The canonical definitions live in
`mathdoc_agent/mathagents/definitions.py`; prompt text lives in
`mathdoc_agent/mathagents/prompts.py`; schemas live in
`mathdoc_agent/models/refinement_specs.py` and
`mathdoc_agent/models/payloads.py`.

## Runtime Contract

All OpenAI Agents SDK agents are created by `mathdoc_agent.mathagents.definitions._agent`.
The default model is read from:

```text
MATHDOC_AGENT_MODEL
```

If the variable is unset, the package currently defaults to `gpt-5.5`.

Agents are executed through `mathdoc_agent.mathagents.runner.run_agent_typed`.
The runner accepts:

- OpenAI Agents SDK `Agent` objects;
- fake or test callables;
- objects exposing `.run(payload)`;
- already structured Pydantic-like outputs.

The runner converts the payload to JSON-compatible data, calls the agent, coerces
the result to the requested Pydantic output schema, logs start/completion/failure
events to stderr, and applies theorem-name enrichment to any
`deduced_from_theorem` objects in the returned model.

Agent calls are bounded by:

```text
MATHDOC_AGENT_AGENT_TIMEOUT_SECONDS
```

If unset, the timeout is 600 seconds. Set it to `0` or a negative value to
disable the timeout.

## Pipeline Placement

The default JSON generation path in `mathdoc_agent/pipeline.py` is:

1. Parse source text into a `MathDocument` using `document_parser_agent`.
2. Refine attached proofs using the proof classifier and proof refiners.
3. Resolve proof kinds that do not have direct Lean codegen handlers.
4. Record Mathlib definition reuse using local similarity search, an LLM exact
   match check, and LeanSearch fallback.
5. Export the document to PaperStructure JSON.
6. Rewrite `deduced_from_claim` dependencies into explicit Lean-friendly proof
   steps.
7. Audit public `claim` fields.
8. Repair informal local notation.
9. Audit risky proof-step assertions.
10. Repair proof-sanity issues.
11. Re-run residual `deduced_from_claim` materialization and informal notation
    repair.
12. Run deterministic Lean-facing JSON finalization.

When the caller supplies custom document or proof registries, the pipeline does
not automatically use the default post-processing agents unless they are also
passed explicitly.

## Shared Schema Fragments

Several agents share these nested schema fragments.

### ChildProofSpec

Used when an agent creates child proof nodes.

```json
{
  "id_suffix": "base",
  "kind": "simple",
  "text": "Proof text for this child.",
  "goal": "optional child goal",
  "hypotheses": ["optional local hypotheses"],
  "notes": ["optional notes"]
}
```

`kind` is usually one of the `ProofKind` values in
`mathdoc_agent/models/base.py`.

### LogicalProofStepData

Used for linear proof steps and inserted local assertions.

```json
{
  "type": "assert_statement",
  "name": "optional_local_name",
  "claim": "a proposition-shaped mathematical claim",
  "proof_method": "short justification",
  "lean_term": "optional Lean term proving this step",
  "source_claim": "optional general claim being instantiated",
  "arguments": ["optional local values or hypotheses"],
  "assumption": "for assume_statement steps",
  "variable_name": "for let/fix-style steps",
  "variable_type": "type of the introduced variable",
  "statement": "alternate statement field",
  "deduced_from_claim": ["local/contextual claims used"],
  "deduced_from_theorem": [
    {
      "claim": "general theorem statement",
      "name": "optional human theorem name",
      "description": "how it is used",
      "lean_name": "optional exact Lean/Mathlib declaration name",
      "lean_term": "optional instantiated theorem term"
    }
  ]
}
```

The pipeline should not emit final JSON with `results_used`; proof dependencies
should be represented as `deduced_from_theorem` or rewritten from
`deduced_from_claim` into explicit `have`/lemma steps.

### ParameterData

Used by structure and inductive declarations and by instance parameters.

```json
{
  "name": "G",
  "type": "Type u",
  "binder": "default"
}
```

`binder` may be `default`, `implicit`, or `typeclass`. If omitted, it is treated
as `default`.

### DeducedFromTheoremData

Used by proof agents to name external theorems.

```json
{
  "claim": "the general theorem statement",
  "name": "optional common name",
  "description": "optional usage note",
  "lean_name": "optional exact Lean declaration name",
  "lean_term": "optional Lean term for the instance used"
}
```

`lean_name` is enriched after agent execution when LeanSearch is enabled. The
agent should not invent Lean names. If a theorem is applied to particular local
variables or hypotheses, `lean_term` should contain the term for that instance.

## Main Document Agent

### `document_parser_agent`

Definition:

```python
document_parser_agent = _agent(
    "Document parser",
    prompts.DOCUMENT_PARSER_INSTRUCTIONS,
    DocumentRefinementSpec,
)
```

Used by:

- `UnknownDocumentHandler` in `mathdoc_agent/handlers/document_handlers.py`.
- The default document handler registry for `DocumentKind.unknown`.

Expected input payload:

```json
{
  "node": {
    "id": "doc.root",
    "kind": "unknown",
    "status": "raw",
    "title": "optional title",
    "text": "source Markdown or prose for this node",
    "data": {},
    "children": [],
    "proof": null,
    "notes": []
  },
  "context": {
    "document_title": "optional title",
    "ancestor_titles": [],
    "available_labels": ["previous labels"],
    "nearby_statements": ["previous theorem-like statements"]
  },
  "task": "Decompose this mathematical document node into local child nodes."
}
```

Function:

- Decompose a raw document node into local child nodes.
- Classify sections, subsections, paragraphs, definitions, structures, instances,
  inductive types, theorem-like statements, examples, remarks, proofs, local
  claims, and calculation blocks.
- Attach following proof prose to theorem-like items through `proof_text`.
- Extract Lean-facing metadata for definitions and declarations without placing
  local definitions inside theorem statements.

Output schema: `DocumentRefinementSpec`.

```json
{
  "children": [
    {
      "id_suffix": "thm1",
      "kind": "theorem",
      "title": "optional title",
      "label": "optional source label",
      "text": "source text for this child",
      "statement": "the theorem statement",
      "notes": [],
      "data_entries": [{"key": "term", "value": "value"}],
      "proof_text": "optional proof text attached to theorem-like nodes",
      "name": "optional declaration name",
      "is_class": false,
      "is_prop": false,
      "parameters": [],
      "indices": [],
      "extends": [],
      "fields": [],
      "gives": [],
      "class_name": null,
      "target": null,
      "value": null,
      "constructors": []
    }
  ],
  "notes": []
}
```

Important declaration-specific child fields:

- `structure-definition`: uses `name`, `is_class`, `is_prop`, `parameters`,
  `extends`, and `fields`.
- `instance-definition`: uses `name`, `class_name`, `target`, `parameters`,
  `gives`, and `value`.
- `inductive-type-definition`: uses `name`, `is_prop`, `parameters`, `indices`,
  and `constructors`.

Structured inductive constructor output:

```json
{
  "name": "step_even",
  "arguments": [
    {"name": "n", "type": "Nat", "binder": "default"},
    {"name": "h", "type": "Even n", "binder": "default"}
  ],
  "index_args": ["n + 2"]
}
```

`index_args` is optional and should contain the index values for the constructor
target when the inductive type is indexed. Constructor argument `binder` is
optional and may be `default`, `implicit`, or `typeclass`; omitted means
`default`.

## Proof Classification Agent

### `proof_classifier_agent`

Definition:

```python
proof_classifier_agent = _agent(
    "Proof classifier",
    prompts.PROOF_CLASSIFIER_INSTRUCTIONS,
)
```

Used by:

- `UnknownProofHandler` for proof nodes with kind `unknown`.

Expected input payload:

```json
{
  "node": {
    "id": "doc.root.thm.proof.root",
    "kind": "unknown",
    "status": "raw",
    "text": "proof fragment",
    "goal": "the theorem statement",
    "hypotheses": [],
    "children": [],
    "data": null,
    "notes": []
  },
  "context": {
    "theorem_statement": "ambient theorem statement",
    "ancestor_goals": [],
    "ancestor_hypotheses": [],
    "sibling_summaries": [],
    "local_claims": [],
    "available_document_results": []
  },
  "task": "Classify this proof fragment."
}
```

Function:

- Classify the outermost proof structure.
- Prefer a direct supported class over `unknown`.
- Use `logical_sequence` for ordinary direct proofs.
- Use `specialize` when the proof instantiates an already proved universal or
  implicational claim at specific local values or hypotheses.

Output schema: the handler expects a `ClassificationSpec`.

```json
{
  "kind": "logical_sequence",
  "confidence": 0.9,
  "notes": []
}
```

`kind` is normalized to a `ProofKind`; unsupported aliases are handled by the
proof-resolution pass later.

## Proof Refinement Agents

### `induction_agent`

Definition:

```python
induction_agent = _agent(
    "Induction proof refiner",
    prompts.INDUCTION_INSTRUCTIONS,
    InductionRefinementSpec,
)
```

Used by:

- `InductionHandler` for proof kind `induction`.

Expected input payload:

```json
{
  "node": {"kind": "induction", "text": "proof by induction ..."},
  "context": {"theorem_statement": "...", "local_claims": []}
}
```

Function:

- Identify the induction variable and optional induction principle.
- Extract induction hypotheses.
- Split base cases and step cases into child proof fragments.
- Preserve explicit case text rather than inventing missing cases.

Output schema: `InductionRefinementSpec`.

```json
{
  "variable": "n",
  "principle": "Nat.rec",
  "induction_hypotheses": ["the induction hypothesis in the step case"],
  "base_cases": [ChildProofSpec],
  "step_cases": [ChildProofSpec],
  "notes": []
}
```

The handler stores `variable`, `principle`, child ids, and induction hypotheses
in `InductionData`.

### `cases_agent`

Definition:

```python
cases_agent = _agent(
    "Cases proof refiner",
    prompts.CASES_INSTRUCTIONS,
    CasesRefinementSpec,
)
```

Used by:

- `CasesHandler` for proof kind `cases`.

Expected input payload:

```json
{
  "node": {"kind": "cases", "text": "split into cases ..."},
  "context": {"theorem_statement": "...", "local_claims": []}
}
```

Function:

- Identify the object or proposition split on.
- Extract each case as a child proof fragment.
- Record why the cases are exhaustive when this is stated.
- Avoid inventing cases not present in the source.

Output schema: `CasesRefinementSpec`.

```json
{
  "split_on": "h",
  "exhaustive_reason": "law of excluded middle",
  "cases": [ChildProofSpec],
  "notes": []
}
```

### `simple_proof_agent`

Definition:

```python
simple_proof_agent = _agent(
    "Simple proof refiner",
    prompts.SIMPLE_PROOF_INSTRUCTIONS,
    SimpleProofRefinementSpec,
)
```

Used by:

- `SimpleProofHandler` for `simple`, `theorem_application`, and
  `definition_unfolding`.
- `LogicalSequenceHandler` for `logical_sequence`.

Expected input payload:

```json
{
  "node": {
    "kind": "logical_sequence",
    "text": "direct proof fragment",
    "goal": "current goal"
  },
  "context": {
    "theorem_statement": "...",
    "ancestor_goals": [],
    "local_claims": [],
    "available_document_results": []
  }
}
```

Function:

- Convert direct proof text into method hints, theorem/hypothesis references,
  explicit proof steps, and unresolved details.
- Preserve each real mathematical step.
- Use `deduced_from_theorem` for standard external theorems and
  `deduced_from_claim` only for local/contextual claims that still require
  rewrite.
- Keep every `claim` proposition-shaped; method names and tactics belong in
  `proof_method`, not `claim`.
- Include `lean_name` only when it is an exact Lean/Mathlib theorem name found
  by LeanSearch; include `lean_term` when an instantiated theorem term is used.

Output schema: `SimpleProofRefinementSpec`.

```json
{
  "method": "direct argument",
  "hints": ["optional hints"],
  "referenced_lemmas": ["human lemma names"],
  "referenced_hypotheses": ["local hypothesis names or descriptions"],
  "deduced_from_claim": ["local claim dependencies"],
  "deduced_from_theorem": [DeducedFromTheoremData],
  "proof_steps": [LogicalProofStepData],
  "unresolved_details": []
}
```

The handler converts this to `SimpleProofData` and may further decompose coarse
proof steps into children when the source clearly contains multiple local proof
chunks.

### `calculation_agent`

Definition:

```python
calculation_agent = _agent(
    "Calculation proof refiner",
    prompts.CALCULATION_INSTRUCTIONS,
    CalculationRefinementSpec,
)
```

Used by:

- `CalculationHandler` for proof kind `calculation`.

Expected input payload:

```json
{
  "node": {"kind": "calculation", "text": "calculation chain"},
  "context": {"theorem_statement": "...", "local_claims": []}
}
```

Function:

- Extract a calculation or relation chain into adjacent steps.
- Preserve relation direction and side conditions.
- Put external theorem dependencies in `deduced_from_theorem`.
- Put local dependencies in `deduced_from_claim` only when they still require
  post-processing.

Output schema: `CalculationRefinementSpec`.

```json
{
  "calculation_kind": "inequality chain",
  "steps": [
    {
      "lhs": "a",
      "relation": "<=",
      "rhs": "b",
      "justification": "by monotonicity",
      "side_conditions": [],
      "deduced_from_claim": [],
      "deduced_from_theorem": []
    }
  ],
  "unresolved_details": []
}
```

Allowed `relation` values are `=`, `<=`, `<`, `>=`, `>`, `<->`, `->`, and
`equiv_mod`.

### `specialize_agent`

Definition:

```python
specialize_agent = _agent(
    "Specialization proof refiner",
    prompts.SPECIALIZE_INSTRUCTIONS,
    SpecializeRefinementSpec,
)
```

Used by:

- `SpecializeHandler` for proof kind `specialize`.

Expected input payload:

```json
{
  "node": {
    "kind": "specialize",
    "text": "instantiate h at x using hx",
    "goal": "current goal"
  },
  "context": {
    "local_claims": ["available general claims"],
    "available_document_results": []
  },
  "task": "Extract a named specialization without using Lean's destructive specialize tactic."
}
```

Function:

- Model Lean's specialization pattern as an additional named local lemma.
- Never express this as the destructive Lean `specialize` tactic.
- Return a new `have`-style assertion with a `name` for the specialized lemma
  and a `lean_term` proving it from the original claim.
- Preserve the original general claim.

Output schema: `SpecializeRefinementSpec`.

```json
{
  "name": "hx_specialized",
  "lean_term": "(h x hx)",
  "claim": "the specialized proposition",
  "source_claim": "the already proved general claim",
  "arguments": ["x", "hx"],
  "unresolved_details": [],
  "notes": []
}
```

The handler validates that `name` and `lean_term` are non-empty and stores the
result as `SpecializeData`.

### `structured_proof_agent`

Definition:

```python
structured_proof_agent = _agent(
    "Structured proof refiner",
    prompts.STRUCTURED_PROOF_INSTRUCTIONS,
    StructuredProofRefinementSpec,
)
```

Used by:

- `StructuredProofHandler` for supported structured proof kinds.

Structured proof kinds handled by the default registry:

```text
contradiction, contrapositive, extensionality, existence, uniqueness,
equivalence, construction, minimal_counterexample, infinite_descent,
exhaustion, counting, pigeonhole, invariant, monotonicity_bounding,
reduction, diagram_chase, epsilon_delta, generic_element, local_to_global,
maximal_minimal, compactness, density, approximation, universal_property,
algorithmic, probabilistic, genericity_ae, diagrammatic_geometric
```

Expected input payload:

```json
{
  "node": {"kind": "contradiction", "text": "structured proof fragment"},
  "context": {"theorem_statement": "...", "local_claims": []},
  "proof_kind": "contradiction",
  "task": "Refine this structured proof fragment."
}
```

Function:

- Extract the core components of the supplied structured proof kind.
- Preserve assumptions, conclusions, witnesses, contradiction assumptions,
  invariants, reductions, constructions, and child proof fragments.
- Use child components only for real subproofs or named local claims.
- Avoid wrapping a proof in recursive child nodes with the same goal.

Output schema: `StructuredProofRefinementSpec`.

```json
{
  "strategy": "proof by contradiction",
  "summary": "short summary",
  "components": [ChildProofSpec],
  "assumptions": ["temporary assumptions"],
  "conclusions": ["derived conclusions"],
  "witness": "optional witness",
  "contradiction_assumption": "optional assumption",
  "full_claim": "optional full claim",
  "claim": "optional local claim",
  "variable_name": "optional generic variable",
  "candidate_variables": [],
  "bound_claim": "optional bound",
  "reduced_to": "optional reduced goal",
  "proof_of_reduction": null,
  "proof": null,
  "invariant": "optional invariant",
  "construction": "optional construction",
  "metadata": [{"key": "original", "value": "value"}],
  "unresolved_details": [],
  "notes": []
}
```

The handler converts this to `StructuredProofData`, creating child proof nodes
for `components`, `proof`, and `proof_of_reduction` as needed.

## Proof Resolution Agents

### `proof_resolution_agent`

Definition:

```python
proof_resolution_agent = _agent(
    "Unsupported proof resolver",
    prompts.PROOF_RESOLUTION_INSTRUCTIONS,
    ProofResolutionSpec,
)
```

Used by:

- `resolve_unhandled_proof_tree` when a proof kind does not have a direct Lean
  codegen handler.
- The `"default"` entry in `definitions.proof_resolution_agents`.

Expected input payload:

```json
{
  "node": {"kind": "compactness", "text": "already refined proof text"},
  "context": {"theorem_statement": "...", "local_claims": []},
  "proof_kind": "compactness",
  "supported_child_kinds": [
    "calculation",
    "cases",
    "construction",
    "contradiction",
    "definition_unfolding",
    "epsilon_delta",
    "equivalence",
    "existence",
    "induction",
    "local_claim",
    "logical_sequence",
    "reduction",
    "simple",
    "specialize",
    "theorem_application",
    "uniqueness"
  ],
  "task": "Express this already-refined proof using simpler proof structures with Lean codegen handlers."
}
```

Function:

- Rewrite a specialized or unsupported proof node into simpler structures that
  Lean codegen already handles.
- Preserve the original mathematical content and local claims.
- Prefer `proof_steps` for short linear arguments and `components` for real
  subproofs.
- Do not recursively produce a component with the same unsupported kind and the
  same goal.

Output schema: `ProofResolutionSpec`.

```json
{
  "strategy": "logical_sequence",
  "summary": "how the unsupported method was exposed",
  "proof_steps": [LogicalProofStepData],
  "components": [ChildProofSpec],
  "unresolved_details": [],
  "notes": []
}
```

The resolver changes the node kind to `logical_sequence`, stores original proof
metadata under `resolution_metadata`, and marks the node decomposed if child
components are returned.

### Specialized proof resolution agents

These are separate agent objects with the same prompt and output schema as
`proof_resolution_agent`, but they are routed by proof family:

- `combinatorial_proof_resolution_agent`: `counting`, `pigeonhole`,
  `probabilistic`, `genericity_ae`, `algorithmic`.
- `analytic_proof_resolution_agent`: `invariant`, `monotonicity_bounding`,
  `maximal_minimal`, `compactness`, `density`, `approximation`.
- `structural_proof_resolution_agent`: `extensionality`, `generic_element`,
  `diagram_chase`, `local_to_global`, `universal_property`,
  `diagrammatic_geometric`.

Their expected input and output schema are identical to `ProofResolutionSpec`.
The separate objects allow logging, model selection, or future prompt
specialization by family while preserving the same contract.

## Post-Export Repair and Audit Agents

### `deduced_from_claim_rewrite_agent`

Definition:

```python
deduced_from_claim_rewrite_agent = _agent(
    "Deduced-from-claim rewriter",
    prompts.DEDUCED_FROM_CLAIM_REWRITE_INSTRUCTIONS,
    DeducedFromClaimRewriteSpec,
)
```

Used by:

- `rewrite_deduced_from_claims_for_lean` after PaperStructure JSON export.

Expected input payload:

```json
{
  "task": "Rewrite generated PaperStructure JSON entries involving `deduced_from_claim` for Lean code generation.",
  "dependency_entries": [
    {
      "path": "/document/body/0/proof/proof_steps/2",
      "deduced_from_claim": ["local dependency claim"],
      "available_hypotheses": ["claims already available before this step"],
      "container_type": "assert_statement",
      "container": {"type": "assert_statement", "claim": "..."},
      "parent_type": "proof"
    }
  ],
  "rewrite_rules": {
    "hypothesis_duplicate": "If already available, omit it.",
    "instantiation": "Insert a named have/assert_statement with name, claim, and lean_term.",
    "needs_proof": "Insert a separate local theorem/lemma with proof steps."
  }
}
```

Function:

- Remove `deduced_from_claim` dependencies already present in local hypotheses.
- Turn instantiations of available general claims into explicit named
  `assert_statement` steps with `name`, `claim`, and `lean_term`.
- Turn dependencies that must first be proved into separate local theorem nodes.
- Ensure final JSON does not rely on unresolved `deduced_from_claim` fields.

Output schema: `DeducedFromClaimRewriteSpec`.

```json
{
  "patches": [
    {
      "path": "/document/body/0/proof/proof_steps/2",
      "action": "insert_have_before",
      "deduced_from_claim": [],
      "remove_claims": ["local dependency claim"],
      "name": "h_specialized",
      "lean_term": "(h x hx)",
      "claim": "the specialized proposition",
      "source_claim": "the general claim",
      "arguments": ["x", "hx"],
      "proof_steps": [],
      "notes": []
    }
  ],
  "notes": []
}
```

Allowed actions:

- `replace_deduced_from_claim`: replace or remove the dependency list.
- `insert_have_before`: insert a named assertion before the current object.
- `insert_specialize_before`: accepted for compatibility but treated as a
  named assertion, not Lean's destructive `specialize` tactic.
- `insert_lemma_before`: insert a named theorem with its own proof steps.

After applying patches, the pipeline deterministically materializes any
remaining `deduced_from_claim` dependencies as explicit assertions.

### `claim_audit_agent`

Definition:

```python
claim_audit_agent = _agent(
    "Lean claim auditor",
    prompts.CLAIM_AUDIT_INSTRUCTIONS,
    ClaimAuditSpec,
)
```

Used by:

- `audit_claims_for_lean` after `deduced_from_claim` rewrite.

Expected input payload:

```json
{
  "task": "Audit generated PaperStructure JSON claim fields for Lean CodegenCore/PaperCodes proposition compatibility.",
  "claim_entries": [
    {
      "path": "/document/body/0/proof/proof_steps/1/claim",
      "claim": "current claim text",
      "container_type": "assert_statement",
      "container": {"type": "assert_statement", "claim": "current claim text"},
      "parent_type": "proof",
      "can_replace_assertion_with_steps": true
    }
  ],
  "patch_rules": {
    "replace_claim": "Use when the field should remain one proposition.",
    "replace_assertion_with_steps": "Use only for assert_statement containers whose claim should be refined into smaller proof steps."
  }
}
```

Function:

- Audit every public JSON `claim` field before Lean codegen.
- Ensure claims are mathematical propositions, not instructions, methods,
  tactic-like text, side-condition labels, or multiple proof steps.
- Repair display notation and local notation when a scoped identifier is
  available in context.

Output schema: `ClaimAuditSpec`.

```json
{
  "patches": [
    {
      "path": "/document/body/0/proof/proof_steps/1/claim",
      "action": "replace_claim",
      "claim": "clean proposition",
      "proof_steps": [],
      "notes": []
    }
  ],
  "notes": []
}
```

Allowed actions:

- `replace_claim`: replace only the claim string.
- `replace_assertion_with_steps`: replace the enclosing `assert_statement` with
  a proof object containing smaller `LogicalProofStepData` steps.

### `informal_notation_repair_agent`

Definition:

```python
informal_notation_repair_agent = _agent(
    "Informal notation repairer",
    prompts.INFORMAL_NOTATION_REPAIR_INSTRUCTIONS,
    InformalNotationRepairSpec,
)
```

Used by:

- `repair_informal_notation_for_lean`, usually twice in the default pipeline.

Expected input payload:

```json
{
  "task": "Repair informal local notation in generated PaperStructure JSON string fields before Lean codegen.",
  "notation_entries": [
    {
      "path": "/document/body/0/proof/proof_steps/1/claim",
      "field": "claim",
      "text": "C_n is finite",
      "container_type": "assert_statement",
      "container": {"type": "assert_statement", "claim": "C_n is finite"},
      "parent_type": "proof"
    }
  ],
  "repair_rules": {
    "replacement": "Return text for the same field with scoped ASCII identifiers or precise prose."
  }
}
```

Function:

- Remove display-only or locally ambiguous notation from Lean-facing string
  fields.
- Repair pseudo-subscripts, LaTeX commands, norm bars, tensor abbreviations,
  informal multi-argument calls, quotient abbreviations, and assignment-shaped
  assertion text.
- Preserve mathematical meaning and produce ASCII identifiers or precise prose.

Output schema: `InformalNotationRepairSpec`.

```json
{
  "patches": [
    {
      "path": "/document/body/0/proof/proof_steps/1/claim",
      "replacement": "Cn is finite",
      "notes": []
    }
  ],
  "notes": []
}
```

The orchestration layer also runs deterministic cleanup after the LLM patches,
so residual recognizable informal notation is repaired even when the agent is
disabled or incomplete.

### `proof_sanity_audit_agent`

Definition:

```python
proof_sanity_audit_agent = _agent(
    "Proof-step sanity auditor",
    prompts.PROOF_SANITY_AUDIT_INSTRUCTIONS,
    ProofSanityAuditSpec,
)
```

Used by:

- `audit_proof_steps_for_counterexamples` after informal notation repair.

Expected input payload:

```json
{
  "task": "Audit generated proof-step assertions for counterexamples, over-strong claims, and unbound local variables before Lean codegen.",
  "assertion_entries": [
    {
      "path": "/document/body/0/proof/proof_steps/3",
      "claim": "for all c, ...",
      "risk_reasons": ["claim quantifies over a new variable not visible in local context"],
      "container": {"type": "assert_statement", "claim": "for all c, ..."},
      "dependencies": {"proof_method": "obvious"},
      "available_context": ["previous local assumptions"],
      "parent_type": "proof",
      "parent_claim": null
    }
  ],
  "patch_rules": {
    "mark_needs_review": "Use when risky but exact repair is unclear.",
    "replace_claim": "Use only when the intended weaker/local claim is obvious.",
    "replace_assertion_with_steps": "Use only when the assertion bundles smaller claims present in context."
  }
}
```

Function:

- Check risky helper assertions before they become Lean proof obligations.
- Look for over-strong claims, new unbound variables, obvious counterexamples,
  informal notation, and universal theorem-shaped assertions created from local
  side conditions.
- Avoid flagging assertions merely because their proof is difficult.

Output schema: `ProofSanityAuditSpec`.

```json
{
  "patches": [
    {
      "path": "/document/body/0/proof/proof_steps/3",
      "action": "mark_needs_review",
      "reason": "unbound variable c",
      "claim": null,
      "proof_steps": [],
      "suggested_repair": "Use the local c already introduced or add an explicit binder step.",
      "notes": []
    }
  ],
  "notes": []
}
```

Allowed actions:

- `mark_needs_review`
- `replace_claim`
- `replace_assertion_with_steps`

The number of entries audited is bounded by:

```text
MATHDOC_AGENT_PROOF_SANITY_MAX_ENTRIES
```

The default limit is 40. Set it to `0` to skip this audit.

### `proof_sanity_repair_agent`

Definition:

```python
proof_sanity_repair_agent = _agent(
    "Proof-step sanity repairer",
    prompts.PROOF_SANITY_REPAIR_INSTRUCTIONS,
    ProofSanityAuditSpec,
)
```

Used by:

- `repair_proof_sanity_issues` after the proof-sanity audit.

Expected input payload:

```json
{
  "task": "Repair proof-step assertions that were marked risky before Lean codegen. Return concrete replacements, not review flags.",
  "assertion_entries": [
    {
      "path": "/document/body/0/proof/proof_steps/3",
      "claim": "risky claim",
      "container": {"type": "assert_statement", "claim": "risky claim"},
      "issues": [
        {
          "reason": "unbound variable",
          "suggested_repair": "make the variable local",
          "notes": []
        }
      ]
    }
  ],
  "patch_rules": {
    "replace_claim": "Use when one scoped replacement claim fixes the issue.",
    "replace_assertion_with_steps": "Use when a missing local definition/witness-introduction step must be inserted before the repaired assertion."
  }
}
```

Function:

- Turn assertions marked by the sanity audit into concrete repairs.
- Prefer a weaker scoped claim or an explicit local definition/witness
  introduction followed by the repaired assertion.
- Do not return `mark_needs_review`; this pass is intended to remove review
  annotations before final JSON.

Output schema: `ProofSanityAuditSpec`, restricted in practice to:

```json
{
  "patches": [
    {
      "path": "/document/body/0/proof/proof_steps/3",
      "action": "replace_claim",
      "reason": "unbound variable",
      "claim": "scoped local replacement claim",
      "proof_steps": [],
      "suggested_repair": null,
      "notes": []
    }
  ],
  "notes": []
}
```

## Agent-Like LLM Components

### Local Mathlib definition reuse matcher

This is not an OpenAI Agents SDK `Agent`, but it is an LLM-backed component in
`mathdoc_agent/orchestration/mathlib_reuse.py`.

Used by:

- `record_mathlib_definitions` before PaperStructure JSON export.

Function:

- For each ordinary `definition` node, conservatively check whether Mathlib
  already has a matching declaration.
- Prefer local similarity search through the LeanAide server endpoint:

```text
http://localhost:7654/run-sim-search
```

- Ask an OpenAI chat-completions LLM to decide whether any returned candidate is
  the exact declaration described by the query.
- If the local search fails to find a match, fall back to LeanSearch and run the
  same exact-match LLM check.
- If a compatible definition-like result is found, annotate the definition data
  with `lean_name`, `mathlib_kind`, and `mathlib_type` so generated code can use
  the Mathlib declaration instead of duplicating it.

Environment variables:

```text
OPENAI_API_KEY
MATHDOC_AGENT_LOCAL_SIMILARITY_URL
MATHDOC_AGENT_LOCAL_LEANSEARCH_MODEL
MATHDOC_AGENT_LEANSEARCH_DEFINITION_CACHE
MATHDOC_AGENT_LOCAL_DEFINITION_CACHE
MATHDOC_AGENT_LEANSEARCH_DEFINITION_SEED
```

Expected LLM input object:

```json
{
  "query": "Mathlib definition named Basis: a basis is ...",
  "candidates": [
    {
      "index": 0,
      "name": "Module.Basis",
      "kind": "structure",
      "type": "...",
      "docString": "..."
    }
  ],
  "instructions": "Decide whether any candidate is exactly the Lean/Mathlib declaration described by the query..."
}
```

Expected LLM output object:

```json
{
  "match": true,
  "index": 0,
  "name": "Module.Basis",
  "reason": "The declaration name and type match the requested basis structure."
}
```

Only `match: true` with a valid candidate index is accepted. The result is then
filtered again for definition-like kind, compatible name, and compatible type.

## Non-Agent LeanSearch Enrichment

`run_agent_typed` calls `enrich_deduced_from_theorems` on every typed agent
output. This is a helper, not a separate LLM agent.

Function:

- Walk the returned Pydantic model.
- Find objects in `deduced_from_theorem`.
- Build a LeanSearch query from `lean_name`, `name`, `claim`, and
  `description`.
- Query LeanSearch through `mathdoc_agent/mathagents/leansearch.py`.
- If the top theorem-like result is a theorem or lemma, fill `lean_name`.
- Cache query results in memory.

Environment variable:

```text
MATHDOC_AGENT_LEANSEARCH_DEDUCED_THEOREMS
```

This is enabled by default. Set it to `0`, `false`, or `no` to disable theorem
dependency enrichment.

The helper should not be used to invent theorem names. Its purpose is to attach
an exact Lean name only when the search helper returns one.

## Local Claim Agent Slot

The proof registry contains a `LocalClaimHandler`, but the default registry
passes `local_claim_agent=None`.

If a custom local claim agent is supplied, it receives:

```json
{
  "node": {"kind": "local_claim", "text": "local claim and proof text"},
  "context": {"theorem_statement": "...", "local_claims": []}
}
```

Expected output schema: `LocalClaimRefinementSpec`.

```json
{
  "statement": "the local claim statement",
  "label": "optional label",
  "proof": ChildProofSpec,
  "notes": []
}
```

With no agent, local claims are passed through or decomposed deterministically by
the handler.
