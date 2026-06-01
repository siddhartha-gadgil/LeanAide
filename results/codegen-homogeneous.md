# Codegen case-study report: `homogeneous`

This report treats the completed `homogeneous` run as an example for improving
the general `mathdoc_agent` -> LeanAide translation/codegen pipeline. The goal is
not to add file-specific rules for `homogeneous`, but to identify reusable
interfaces, validators, diagnostics, and failure policies.

Inputs analysed:

- `.logs/2026-06-01.log`
- `results/homogeneous.json`
- `CodeGen/homogeneous.lean`
- `mathdoc_agent/`
- `LeanAideCore/LeanAideCore/`
- `LeanAide/`

Lean code was not modified.

## Executive Summary

The run reached:

```text
LeanAide.documentCode for key document worked; returned : true
```

This is only a syntactic/codegen-completion signal. It is not a successful
formalization signal.

The generated file has:

- 8694 lines.
- 14 elaborated declarations.
- 11 theorem declarations.
- 46 raw `sorry` occurrences.
- 39 `repeat (sorry)` occurrences.
- 4 top-level `#check "Error: codegen: ..."` diagnostic blocks.
- 16 proof-step `trace "Error in processing:..."` diagnostics.
- 2 unresolved metavariable/projection failures.
- A bottom diagnostic section listing `Sorries (31 goals)`.

The bottom section of `CodeGen/homogeneous.lean` is the most useful artifact:
it lists the propositions corresponding to the remaining sorries after
elaboration. These goals reveal not just that proof search failed, but what kind
of proof obligation was generated. The log adds the prompts and all attempted
translations, so it is possible to diagnose translation drift and missing schema
structure without rerunning Lean.

## General Failure Classes

### 1. Success Status Does Not Mean Proof Complete

Lean codegen currently converts several hard failures into generated diagnostics
inside the Lean file.

Examples from this run:

- Failed top-level theorem translations were emitted as `#check` strings.
- Failed proof steps were emitted as `trace "Error in processing:..."`.
- Failed proof search emitted `repeat (sorry)`.
- Generated declarations were still registered as successful.

Relevant Lean paths:

- `LeanAideCore/LeanAideCore/CodegenCore.lean:313`: command generation catches
  errors and emits diagnostic commands.
- `LeanAideCore/LeanAideCore/CodegenCore.lean:258`: proof search falls back to
  `repeat (sorry)`.
- `LeanAideCore/LeanAideCore/PaperCodes.lean:360`: theorem definitions are
  added once syntax is generated, without rejecting sorries.

Universal recommendation:

Add a strict codegen mode with a structured result:

```json
{
  "status": "complete" | "incomplete" | "failed",
  "generated_declarations": [...],
  "failed_declarations": [...],
  "sorry_goals": [...],
  "translation_attempts": [...],
  "proof_step_failures": [...]
}
```

In strict mode, fail if any generated declaration contains:

- `sorry`
- `admit`
- `?m`
- `#check "Error: codegen: ..."`
- `trace "Error in processing:..."`

Keep diagnostic strings out of the generated Lean file where possible. Write
them to a sidecar report or JSON diagnostic file.

### 2. The Generated Lean Footer Should Be Promoted To First-Class Diagnostics

The bottom of `CodeGen/homogeneous.lean` contains an elaboration summary:

- declarations generated,
- elaboration logs,
- invalid projection/typeclass errors,
- `Sorries (31 goals)`,
- the statement of each sorry goal.

The 31 goals are more actionable than line-level `sorry` counts. They show that
the failures group into reusable classes:

- elementary local algebra goals,
- induction step goals with missing local binders,
- impossible/generated false group identities,
- probability and finite-sum estimates,
- quotient/commutator subgroup closure,
- quotient-lift uniqueness,
- quotient seminorm construction,
- final dependency-driven corollary goals.

Universal recommendation:

Parse the elaboration footer into structured diagnostics. For each sorry goal,
record:

- owning declaration,
- local context,
- target proposition,
- source JSON path if available,
- proof step that produced it,
- whether the target contains generated helper assertions,
- whether the target contains metavariables.

This should feed back into Python as a training/evaluation signal: a proof step
that creates a sorry goal with unresolved pseudo-notation, false universal
quantification, or unsupported theory should be classified differently from a
small arithmetic goal.

### 3. Prompt Policy Is Inconsistent About Sorries

The logs show two conflicting proof policies.

One prompt asks the LLM to replace `sorry` and says:

```text
Complete the Proof: Ensure the proof is complete and leaves no remaining sorry
or open goals.
```

But `LeanAideCore/LeanAideCore/LLMTactic.lean` also defines a `prompt_sorry`
whose instruction says that the model may use `sorry` strategically and should
"move forward" even if intermediate steps rely on `sorry`.

Also, statement-translation prompts are example-driven and commonly include
`with proof by sorry`, so the theorem translator is optimized for elaborating
statement shapes, not for proof-complete output or semantic faithfulness.

Universal recommendation:

Separate modes explicitly:

- `translate_statement`: may use `by sorry` internally only to elaborate a type.
- `draft_proof`: may use sorries, but output must be marked incomplete.
- `strict_proof`: must not output sorries; failure is a valid result.
- `diagnostic_proof`: may output a proof skeleton plus named missing lemmas.

The codegen path should not mix these modes. If a prompt allows sorries, its
result must not be registered as a proved theorem.

### 4. Natural-Language Proof JSON Still Contains Informal Local Notation

The generated JSON and the diagnostic source blocks contain terms such as:

- `C_n`, `C_{n+1}`,
- `wy C_n z w^{-1}`,
- `f(0,n)`,
- `VQ = A tensor_Z Q`,
- `B := the metric completion of W`,
- `||phi(g)||_B`,
- `G_ab`,
- `A/T(A)`.

These are useful for humans, but not enough for Lean codegen. When such terms
appear in fields that Lean will translate as propositions, codegen either fails
or fabricates unrelated statements.

Universal Python recommendation:

Add a final Lean-facing JSON lint pass. Fields used by Lean codegen should
either be:

- valid Lean expressions/types,
- structured math objects with explicit Lean construction fields,
- or marked unsupported.

Reject or quarantine proof steps whose codegen-facing claims contain:

- subscript pseudo-variables,
- prose equations such as `VQ = A tensor_Z Q`,
- unbound local functions like `f(0,n)`,
- display notation with no Lean term,
- witness strings containing assignment syntax in the name/value.

### 5. `deduced_from_claim` Is Still Reintroduced After Rewriting

`results/homogeneous.json` has:

- 93 residual `deduced_from_claim` fields.
- 0 `results_used` fields.

The absence of `results_used` is good. The residual `deduced_from_claim` fields
are not good for current codegen.

The pipeline runs:

- `rewrite_deduced_from_claims_for_lean` in `mathdoc_agent/pipeline.py:523`.
- `audit_claims_for_lean` afterwards in `mathdoc_agent/pipeline.py:527`.

The claim-audit pass can replace assertions with proof steps, and
`mathdoc_agent/orchestration/claim_audit.py:98` preserves
`deduced_from_claim` on inserted steps. Thus the rewrite pass can clean the JSON
and the later audit can reintroduce the same problem.

Universal recommendation:

Run a final normalization pass after all agents:

1. remove local-hypothesis duplicates,
2. materialize remaining `deduced_from_claim` as explicit named haves,
3. convert genuine instantiations into `specialize`-style named haves with
   `lean_term`,
4. reject any remaining `deduced_from_claim` before Lean codegen.

This should be enforced as a schema invariant:

```text
Lean-facing JSON must not contain deduced_from_claim.
```

### 6. `deduced_from_theorem` Needs Exact Terms, Not Just Theorem Names

The JSON contains many `deduced_from_theorem` entries. Often they have a theorem
name or description, but no Lean term for the actual instantiated use.

The Lean handler in `LeanAideCore/LeanAideCore/PaperCodes.lean:854` reads
`deduced_from_theorem`. If `lean_term` is absent, it may treat `lean_name` as a
term. That is not enough: a theorem declaration name is usually not itself a
proof of the current assertion.

Universal recommendation:

Use this distinction consistently:

- `lean_name`: a declaration name found in Mathlib or earlier generated code.
- `lean_term`: the exact local proof term for this proof step, with all
  arguments and hypotheses supplied.
- `lean_name` without `lean_term`: suggestion only, not a proof.

Codegen should:

- use `lean_term` for local `have`/`exact`;
- use `lean_name` only as a search hint;
- fail or defer the proof step if no applicable term is available.

### 7. Translation Drift Is A Core Problem

The logs contain all attempted translations. They show recurring drift:

- a source `l : G -> R` became `l : GroupSeminorm G`;
- a source `p : A -> R` became `p : AddGroupSeminorm A` or `p : Seminorm Z A`;
- integer homogeneity became natural-number homogeneity;
- multiplicative target groups were translated through additive `TensorProduct`
  constructions;
- generated theorem attempts alternated between `Additive B` and
  `Multiplicative B`;
- local predicates such as "homogeneous length function" were translated to
  unknown names like `HomogeneousLengthFunction G`, then later to `(G -> R) ->
  Prop`.

Universal recommendation:

Statement translation needs caller-provided constraints and validation:

- expected variables and their types,
- required constants/predicates,
- forbidden replacements,
- expected binder polarity/order,
- expected theorem family shape,
- allowed Mathlib substitutions only when explicitly recorded.

For example, if the source says `l : G -> R`, translation should not silently
replace it by `GroupSeminorm G` unless a previous step established that this is
the intended representation and recorded the coercion. If the source has
integer homogeneity, a theorem with only `Nat` homogeneity should be rejected or
flagged as weaker.

A good way to reduce this drift is to include previously generated Lean code in
later prompts, but the context should be curated and constraint-oriented rather
than a raw dump of the whole file. Later translation prompts should receive the
available declaration environment:

```text
Previously generated Lean declarations available:
- IsPseudoLengthFunction :
  {G : Type u} -> [Group G] -> (G -> ℝ) -> Prop
- IsLengthFunction :
  {G : Type u} -> [Group G] -> (G -> ℝ) -> Prop
- IsHomogeneousPseudoLength :
  {G : Type u} -> [Group G] -> (G -> ℝ) -> Prop
```

and explicit constraints:

```text
Use these names exactly when relevant.
Do not replace `l : G -> ℝ` by bundled seminorm structures unless this
representation change has already been recorded.
Do not change integer homogeneity to natural-number homogeneity.
Preserve additive versus multiplicative notation from the source.
```

Universal prompt recommendation:

- include prior generated declarations with names and types;
- include selected Mathlib declarations that have been accepted for reuse;
- include earlier local theorem names and exact Lean statements;
- suppress earlier theorem proofs by replacing them with `by sorry` when they
  are included only as context, since later translation usually needs the
  theorem name and statement rather than its proof term;
- include "must use" and "must not replace" constraints;
- keep this as a compact declaration environment, not the entire generated
  Lean file;
- validate after generation that the output used the intended names and did not
  silently switch representations.

### 8. Generated Helper Claims Can Be False

The bottom sorry list and theorem bodies show helper claims that are not merely
hard, but false or vastly over-generalized. A representative example is a group
identity of the form:

```lean
forall (c : G) (m k : Z), x * y * x^-1 = c * y
```

This kind of claim can make later goals provable only through contradiction or
`sorry`; it is a proof-generation bug, not just an automation limitation.

Universal Python recommendation:

Add a proof-step sanity auditor before Lean codegen:

- reject helper claims that quantify over new arbitrary variables not present in
  the source step;
- reject claims that turn a local definition into an arbitrary universal fact;
- reject "side condition" claims whose variables are not in scope;
- reject assertions that are stronger than their justification;
- generate counterexample prompts/tests for each intermediate assertion.

This aligns with the stress-test principle: try to construct counterexamples to
each lemma or local assertion as stated before sending it to codegen.

### 9. Induction Needs A Structured Contract

The failed induction example shows the general issue. Python exports:

```json
{
  "type": "induction_proof",
  "on": "n",
  "base_case_proof": ...,
  "induction_step_proof": ...
}
```

but the subproofs still refer to informal objects like `C_n`, `C_{n+1}`, and
`n`. The Lean handler introduces branch names internally, but the JSON does not
say how the source variables map to Lean branch variables or the induction
hypothesis.

Universal recommendation:

Use an induction schema with:

- induction variable,
- motive/claim as a Lean proposition family,
- base index name,
- step predecessor name,
- step successor name,
- induction hypothesis name and type,
- local definitions indexed by the induction variable,
- base and step targets as Lean-facing propositions.

Do not let subproofs refer to `C_n` or `n+1` unless those are mapped to Lean
terms in the branch context.

### 10. Construction Proofs Need Structured Witnesses

The failed construction example generated:

```text
Let B be B := the metric completion of W, where ...
```

because the JSON had `variable_name = "B"` and the construction string also
started with `B := ...`.

This is a general schema issue. Natural-language witness strings are not enough
for Lean.

Universal recommendation:

Represent constructed objects as:

```json
{
  "name": "B",
  "lean_type": "...",
  "lean_value": "...",
  "description": "...",
  "properties": [...]
}
```

At minimum, reject:

- witness names containing `:=`,
- tuple/display names in a single witness,
- construction strings that define more than one object,
- missing Lean type for a witness used later.

Lean codegen should prefer `lean_value` and `lean_type`. Natural language
description should be diagnostic context only.

### 11. Unsupported Theory Should Be Explicit

The 31 sorry goals include proof obligations from:

- probability and Rademacher random variables,
- finite averaging/random-walk estimates,
- quotient lift and uniqueness,
- commutator subgroup generation/closure,
- quotient seminorm construction,
- tensor extension,
- completion of seminormed spaces,
- Banach-space representation.

These are not ordinary local `simp`/`ring` goals. If the Python side generates
proof steps at this level without known Lean lemmas and exact terms, the Lean
side can only guess or insert sorries.

Universal recommendation:

Add an explicit support-level classification:

```json
{
  "formalization_status": "ready" | "needs_named_lemmas" | "unsupported",
  "missing_primitives": [...],
  "required_theorems": [...]
}
```

For `needs_named_lemmas`, Python should introduce named local lemmas and stop.
For `unsupported`, codegen should emit a diagnostic stub or skip the proof,
not a theorem that appears successful.

## How To Use Prompts And Attempted Translations

The logs contain:

- statement-translation prompts,
- proof-repair prompts,
- all candidate translations,
- frontend elaboration errors for candidates.

These should be machine-consumed, not just printed.

Universal recommendation:

For every statement translation request, store:

```json
{
  "source_statement": "...",
  "prompt_id": "...",
  "candidates": [
    {
      "lean": "...",
      "elaboration_status": "ok" | "failed",
      "errors": [...],
      "semantic_validation": {
        "required_symbols_present": true,
        "forbidden_symbols_absent": true,
        "binder_match": true,
        "strength_relation": "same" | "weaker" | "stronger" | "unknown"
      }
    }
  ]
}
```

Do not choose the first elaborating candidate. Choose the first candidate that
also passes semantic validation.

For proof repair prompts, store whether the prompt allowed sorries. If it did,
the result is incomplete by construction.

## Translation Failure Diagnosis From Prompt Logs

The log records a useful pattern for failed translations:

1. the source text to be translated;
2. the prompt sent to the LLM, usually with retrieved examples;
3. several returned candidate translations;
4. `Trying to elaborate ...`;
5. the frontend errors for each candidate.

This sequence should be treated as a first-class diagnostic artifact. It shows
not only that Lean rejected a candidate, but also why the prompt made that
candidate likely.

For each failure, keep both translation inputs:

- the local/source text without generated-code prelude;
- the enriched text with prelude, generated declarations, selected Mathlib
  declarations, and local context.

If the no-prelude translation invents identifiers, that is expected. If the
with-prelude translation still invents identifiers or changes representation,
then the prelude is missing binding constraints or is being outweighed by
retrieved examples.

### Invented Identifiers From Missing Declaration Context

Example source:

```text
There exists a homogeneous length function l on G.
```

Representative candidates:

```lean
∀ (G : Type u_1) [Group G], ∃ l : LengthFunction G,
  LengthFunction.IsHomogeneous l

∀ (G : Type u_1) [Group G], Nonempty (HomogeneousLengthFunction G)
```

Representative errors:

```text
Function expected at LengthFunction ...
The identifier LengthFunction is unknown

Function expected at HomogeneousLengthFunction ...
The identifier HomogeneousLengthFunction is unknown
```

Diagnosis:

The prompt used generic Mathlib examples but did not give the model the local
generated declaration environment. The model therefore invented natural names
such as `LengthFunction` and `HomogeneousLengthFunction`. These names are
mathematically reasonable, but unavailable in the Lean environment. A later
candidate expanded the predicate as `(l : G -> ℝ) -> Prop`; that elaborates, but
is semantically useless because it forgets the definition.

General prompt improvement:

- include accepted generated declarations and their exact types;
- explicitly say that the model must not invent declaration names;
- tell the model to expand an unavailable concept only if no local declaration
  is provided;
- reject candidates whose target is merely `Prop` or `(l : ...) -> Prop` when
  the source asks for a specific predicate;
- include a list of allowed local names and selected Mathlib names.

### Representation Drift Caused By Retrieved Examples

Example source:

```text
Let A be an abelian group. Let p : A -> R be a homogeneous pseudo-length
function. Then p factors through the quotient A/T(A). The induced function on
A/T(A) is again a homogeneous pseudo-length function.
```

Representative candidates drifted between:

```lean
p : A → R
p : AddGroupSeminorm A
p : Seminorm ℤ A
IsHomogeneousPseudoLengthFunction p
```

Representative errors included:

```text
Function expected at LinearOrderedRing ...
The identifier LinearOrderedRing is unknown

Function expected at IsHomogeneousPseudoLengthFunction ...
The identifier IsHomogeneousPseudoLengthFunction is unknown
```

Diagnosis:

The examples encouraged plausible Mathlib representations, but the source and
the surrounding document were using an unbundled function `p : A -> R`. The
prompt did not state which representation was already chosen for pseudo-length
functions, nor which local predicate should express homogeneity. The LLM
therefore tried several incompatible formalizations. Some are close to existing
Mathlib idioms, but they are not faithful to the document's current formal
representation.

General prompt improvement:

- pass a representation contract with every statement translation;
- mark source variables as fixed and non-replaceable unless an explicit coercion
  or bundled representation has already been introduced;
- include "forbidden substitutions", for example `p : A -> ℝ` must not become
  `p : Seminorm ℤ A` or `p : AddGroupSeminorm A` unless requested;
- require the translator to preserve the codomain and scalar domain;
- validate the candidate against this contract before accepting it.

### Local Context Is Presented As Prose, Not Lean Bindings

Example source:

```text
Fix G : Type u_1
Fix inst : Group G
Fix l : G -> R
Set z := y x y^{-1}.
x = y^{-1} z y
```

Representative candidate:

```lean
∀ {G : Type u_1} [Group G] (l : G → ℝ) ... (x y : G),
  x = y⁻¹ * z * y
```

Representative error:

```text
Type mismatch
  z
has type ?m.1
but is expected to have type G
```

Diagnosis:

The context line `Set z := ...` was available as natural language, but not as a
typed Lean binder or a `let`. The translator reused the name `z` in the target
without binding it. Similar failures occur when prose definitions such as
`f(m,k) := ...`, `c := [x,y]`, or `S_{2n}` appear in the prompt but are not
represented as Lean-local definitions.

General prompt improvement:

- provide local context as a Lean-like environment:

  ```lean
  variable {G : Type u_1} [Group G]
  variable (l : G → ℝ)
  variable (x y : G)
  let z : G := y * x * y⁻¹
  ```

- distinguish assumptions, fixed variables, and local definitions;
- require every identifier used in the output to be either bound in the output,
  listed in the local environment, or a known declaration;
- reject outputs with free identifiers not present in the allowed environment.

### Candidate Extraction Can Damage Otherwise Useful Output

One candidate was returned inside a fenced code block and included local `let`
bindings:

```lean
let c : G := ⁅x, y⁆
let f : ℤ → ℤ → ℝ := fun (m k : ℤ) => l (x ^ m * c ^ k)
...
```

The elaboration log then tried fragments where `f` and `sSum` appeared without
their `let` binders, producing errors such as:

```text
Function expected at f ...
The identifier f is unknown
```

Diagnosis:

This is partly a prompt issue and partly a Lean-side extraction issue. The
prompt says "Give ONLY the Lean code", but candidates can still arrive wrapped
in markdown fences. The theorem elaborator does not consistently apply
`extractLean` before trying theorem expressions, and its line-block fallback can
try subfragments that have lost essential preceding `let` bindings. This
creates misleading secondary errors.

General prompt/codegen improvement:

- strengthen the prompt: "Return a single Lean term or theorem statement; do
  not use markdown fences; do not add explanatory text";
- apply `extractLean` to theorem-statement candidates before elaboration, not
  only to definition commands;
- when trying sub-blocks, preserve dependent `let` bindings or avoid sub-block
  fallback for multi-line theorem expressions;
- classify markdown-fenced output as a format violation separately from a
  mathematical translation failure.

### Complex Constructions Need Structured Translation Tasks

Examples that failed at translation include:

```text
Let VQ := A tensor_Z Q. There exists a seminorm normQ on VQ such that
normQ(a tensor 1)=p(a) for every a in A.
```

and:

```text
There exist a real Banach space B and a group homomorphism phi : G -> (B,+)
such that l(g)=||phi(g)||_B for every g in G.
```

Representative codegen diagnostic:

```text
failed to translate ... to a proposition even with 'full statement'
```

Diagnosis:

These statements combine object construction, quotient/tensor notation, bundled
structures, norm notation, and universal properties. A single theorem-translation
prompt asks the model to infer all missing Lean primitives at once. Retrieved
examples about unrelated Mathlib theorems do not provide the required local
construction schema.

General prompt improvement:

- split translation into subtasks:
  1. identify required objects and their Lean representations;
  2. identify required existing Mathlib declarations;
  3. translate the theorem statement using only those representations;
  4. report unresolved primitives rather than inventing names;
- include source text and generated-code context together;
- ask for a structured response when the translator cannot produce a faithful
  Lean statement, for example:

  ```json
  {
    "status": "needs_primitives",
    "missing": ["Lean representation of A tensor_Z Q", "seminorm on quotient"],
    "partial_statement": "..."
  }
  ```

### Prompt Selection Should Prefer Local Relevance Over Topical Similarity

Several prompts used retrieved examples that were topically related to groups,
quotients, norms, or homogeneity, but not aligned with the local representation
chosen by the document. This caused the translator to follow examples too
literally, because the prompt also says "Follow EXACTLY the examples given."

General prompt improvement:

- rank examples by structural match, not only topic: same binder shape,
  bundled/unbundled representation, additive/multiplicative convention, scalar
  domain, and quotient/construction schema;
- include negative constraints when examples use a nearby but wrong
  representation;
- include a short "current document vocabulary" section before retrieved
  examples;
- lower the authority of retrieved examples by saying they illustrate syntax,
  while the local declaration environment and representation contract are
  binding.

## General Improvements For `mathdoc_agent`

1. Add a final Lean-facing schema lint pass.

   Enforce no residual `deduced_from_claim`, no `results_used`, no informal
   pseudo-notation in codegen fields, no malformed witness names, and no
   theorem dependency without either a validated `lean_term` or explicit
   unresolved status.

2. Add semantic validators for theorem statements.

   Compare source variables, predicates, and expected theorem shape against the
   generated Lean statement. Reject silent replacements such as function to
   bundled seminorm, integer to natural homogeneity, or multiplicative to
   additive target unless explicitly justified.

3. Add proof-step counterexample checks.

   Before Lean codegen, ask whether each generated intermediate assertion is
   stronger than the source, has unbound variables, or has simple
   counterexamples.

4. Make proof schemas more structured.

   Induction, quotient lifts, construction/existence proofs, specialization,
   factorization, and finite-sum/probability estimates need schemas that carry
   Lean-local names, types, and terms.

5. Track dependencies between document results.

   A theorem depending on failed lemmas should be skipped with dependency
   failure, not freshly translated from prose as though dependencies succeeded.

6. Classify unsupported mathematics explicitly.

   When no Lean helper exists for a mathematical construction, emit a named
   missing lemma or unsupported diagnostic instead of a proof JSON that will
   become `repeat (sorry)`.

7. Preserve all translation candidates in diagnostics.

   Use the attempted translations from the logs to improve prompt retrieval,
   validation, and examples. Do not bury them as `#check` strings in generated
   Lean.

8. Pass a compact generated-code context into later prompts.

   Each later statement/proof prompt should receive the already accepted Lean
   declaration environment: generated names and types, selected Mathlib names,
   local theorem names, and exact prior statements. Earlier theorem proofs can
   normally be suppressed and represented as `by sorry` for brevity; the
   important context is the statement and the stable name. This should be
   accompanied by explicit constraints about representations that must be
   preserved. The prompt should not receive the whole generated file unless
   necessary, because raw code dumps add noise and can make the model imitate
   failed attempts.

9. Feed translation-failure diagnostics back into prompt construction.

   Store each failed translation with source text, prompt, retrieved examples,
   candidates, and elaboration errors. Classify failures such as invented
   identifiers, representation drift, free local variables, fenced-code format
   violations, and unsupported constructions. Use these classes to choose repair
   prompts and to improve example retrieval.

## General Improvements For LeanAide Codegen

1. Add strict/incomplete modes.

   In strict mode, no generated declaration with `sorry`, `?m`, diagnostic
   traces, or diagnostic `#check` commands is considered success.

2. Replace `repeat (sorry)` fallback with structured failure.

   `findTacticsI` should return either tactics or a failure object containing
   the target and local context. A separate non-strict mode may still emit
   sorries, but must label the declaration incomplete.

3. Promote sorry-goal extraction.

   The bottom `Sorries (31 goals)` section is valuable. Expose this as JSON from
   codegen, including owner declaration and source JSON path.

4. Keep generated diagnostics out of Lean code.

   `#check "Error: ..."` and `trace "Error in processing: ..."` are useful for
   humans but should not be mixed into the generated code as if they were part
   of the artifact.

5. Treat `lean_name` and `lean_term` differently.

   A `lean_term` may be inserted into a proof. A `lean_name` is only a hint
   unless codegen constructs and checks an application of it.

6. Add semantic validation hooks to translation.

   `translateToPropStrict` checks elaboration. It should also accept optional
   constraints from Python and reject elaborating statements that fail them.

7. Make construction and induction handlers schema-driven.

   Avoid translating witness prose like "Let B be ..." when structured Lean type
   and value fields exist. Avoid induction branch proofs that cannot see the
   branch-local names intended by Python.

8. Log prompt mode and proof completeness.

   If a proof was produced by a prompt that allowed `sorry`, record that fact in
   the declaration metadata and return incomplete status.

9. Normalize theorem candidates before elaboration.

   The theorem-statement path should apply `extractLean` to remove markdown
   fences before calling `elabThm4`. If line-block fallback is retained, it
   should not try fragments that lose required `let` bindings or local context;
   such failures should be reported as candidate-format/extraction failures.

## Minimal Acceptance Criteria For Future Runs

A run should count as successful only if all of the following hold:

1. Every source theorem either has a generated declaration, an explicit
   unsupported/dependency-failed status, or an explicit skipped status.
2. No generated declaration contains `sorry`, `admit`, or unresolved
   metavariables in strict mode.
3. No proof step is converted to a diagnostic `trace`.
4. No top-level codegen failure is converted to a `#check` string.
5. Every statement translation passes semantic validation, not just Lean
   elaboration.
6. Every theorem dependency used as a proof has a checked `lean_term`.
7. Every remaining hard proof obligation appears as a named missing lemma with a
   Lean statement and source JSON path.

## Case-Study Notes From This Run

These examples should guide tests, not special-case code.

- The `lemma_2` induction failure shows the need for a structured induction
  contract and Lean-local branch names.
- The `lemma_4` false group identity shows the need for counterexample/sanity
  checks on generated helper claims.
- The `lemma_5` and `lemma_6` probability goals show the need to mark advanced
  theory as `needs_named_lemmas` or `unsupported` unless exact dependencies are
  available.
- The `lemma_8` and `lemma_9` quotient/commutator goals show the need for
  quotient-lift and subgroup-closure schemas.
- The `lemma_11` quotient seminorm goals show the need to choose one
  representation for pseudo-lengths/seminorms and validate substitutions.
- The `lemma_12`, `lemma_13`, and `theorem_14` failures show that high-level
  construction prose should not be sent directly to theorem translation.
- The `corollary_15` generated theorem shows why downstream theorems must be
  dependency-aware and why `Nat`/`Int`, additive/multiplicative, and bundled/
  unbundled drift must be rejected.
