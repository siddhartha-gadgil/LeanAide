# Codegen diagnosis for `results/homogeneous.json`

Date: 2026-05-26.

Input analysed:

- `results/homogeneous.json`
- `.logs/2026-05-26.log`
- `LeanAideCore/LeanAideCore/PaperCodes.lean`
- `LeanAide/PaperCodes.lean`
- relevant codegen support in `LeanAideCore/LeanAideCore/CodegenCore.lean`

I did not run Lean for this diagnosis. The conclusions below are based on the
interrupted log, the generated JSON, and the codegen implementation.

## Summary

The interrupted run was not stuck in Python. It had already entered the Lean
codegen/elaboration stage and was blocked at an automation probe:

```lean
example : ∀ (G : Type u_1) [inst : Group G],
  commutator G = Subgroup.closure (commutatorSet G) := by try?
```

The last log entries are the frontend starting this `by try?` command and not
returning. The command was generated while translating Definition 5,
`commutatorSubgroup`, after the direct definition translation failed to yield a
usable definition and `defCode` fell back to proving an existential theorem.

There are two classes of problems:

1. Python generation produces natural-language definitions that are too
proposition-like or existence-like for the Lean `definition` codegen path.
2. Lean codegen falls back from failed definition translation to unbounded
automation (`simp?`, `grind?`, `try?`) on hard global goals. The `try?` probe can
hang and there is no timeout or heartbeat guard in the codegen path.

## What the Log Shows

The run starts normally with document/section/paragraph handlers, then begins
the top-level definitions.

Processed successfully:

- Definition 1, `PseudoLength`, translated to:
  `definition IsPseudoLengthFunction : {G : Type u} -> [Group G] -> (G -> ℝ) -> Prop := ...`
- Definition 2, `IsLength`, translated to:
  `def IsLengthFunction {G : Type u} [Group G] (l : G -> ℝ) : Prop := ...`
- Definition 3, `IsHomogeneousPseudoLength`, initially produced variants
  involving `PseudoLengthFunction G`, then recovered to a `(G -> ℝ) -> Prop`
  definition.
- Definition 4, `commutator`, direct definition translation produced
  `def commutatorElement ...`, but the frontend reported messages. `defCode`
  then tried the existential fallback and generated a theorem named
  `exists_commutator`.

The run then reached Definition 5, `commutatorSubgroup`:

```text
Translating to proposition: There exists commutatorSubgroup such that:
Let G be a group. The commutator subgroup [G,G] is the subgroup of G generated
by the set {[x,y] | x,y in G}.
```

LeanAide translated this to:

```lean
∀ (G : Type u_1) [inst : Group G],
  commutator G = Subgroup.closure (commutatorSet G)
```

It elaborated that proposition, then tried automation:

```text
Trying automation tactics
previous definitions/theorems names: #[]
...
example : ... := by simp?
example : ... := by grind?
example : ... := by try?
```

The log ends immediately after the frontend starts `by try?`, so the interrupt
point is the `try?` automation probe.

## Python Stage Issues

### 1. Definitions are not Lean-oriented enough

`results/homogeneous.json` has 8 top-level `definition` objects. The first five
are:

- `PseudoLength`
- `IsLength`
- `IsHomogeneousPseudoLength`
- `commutator`
- `commutatorSubgroup`

The definitions are still prose-level mathematical descriptions. For example:

```text
Let G be a group. The commutator subgroup [G,G] is the subgroup of G generated
by the set {[x,y] | x,y in G}.
```

This is treated by the Lean stage as an existential proposition:

```text
There exists commutatorSubgroup such that: ...
```

That fallback is not a reliable way to introduce definitions. It turns a
definition into a theorem-search/automation problem.

Recommended Python-side improvement:

- Generate definitional objects with an explicit Lean-facing shape when the
  document intends to introduce notation or a structure:
  - parameters/context,
  - target type,
  - defining expression when available,
  - proposition-valued predicate only when the definition is actually a
    predicate.
- Avoid "There exists `<name>` such that" for definitional entries unless the
  mathematical text is genuinely existential.

### 2. Existing Mathlib names are shadowed by generated names

The JSON asks for definitions named `commutator`, `abelianization`,
`torsionSubgroup`, and `TorsionFree`. These are very likely to collide
semantically with existing Mathlib notions or with local names used by
LeanAide's retrieved examples.

In the log, the translated proposition for `commutatorSubgroup` uses:

```lean
commutator G = Subgroup.closure (commutatorSet G)
```

This assumes `commutator` and `commutatorSet` are already meaningful constants.
But the generated Definition 4 was `commutatorElement`, not `commutator`, and
the existential fallback theorem `exists_commutator` does not define a usable
constant `commutator`.

Recommended Python-side improvement:

- Preserve the declared definition name in the Lean-facing output, or record
  the generated Lean name separately and update later references.
- For loaded Mathlib names, use `lean_name`/namespace fields explicitly instead
  of relying on prose names.

### 3. Theorems have no stable names

The generated theorem objects in `homogeneous.json` have labels such as
`Lemma 1`, but the `name` field is absent for the top-level theorems. The Lean
stage therefore asks the LLM/server to invent theorem names during codegen.

Risks:

- extra API calls during codegen,
- unstable names between runs,
- difficult cross-reference resolution,
- local theorem lookup by label may diverge from generated Lean names.

Recommended Python-side improvement:

- Fill a deterministic `name` for every theorem/lemma/corollary before codegen.
- Keep the document label separately as `label`.

### 4. `deduced_from_theorem` is enriched, but not Lean-codegen compatible

There are 138 assertion steps carrying `deduced_from_claim` or
`deduced_from_theorem`. Many theorem dependencies contain a `lean_name`, for
example:

```json
{
  "claim": "For a homogeneous pseudo-length function l, ...",
  "name": "homogeneity",
  "lean_name": "map_zpow"
}
```

However, `LeanAideCore/LeanAideCore/PaperCodes.lean` still has helper code for
`ResultUsed` objects using `mathlib_identifier` and `target_identifier`, not
the newer `lean_name` field. There is no visible codegen handler for
`deduced_from_theorem` or `deduced_from_claim` as fields on an
`assert_statement`.

Recommended Python-side improvement:

- Either emit the shape that Lean codegen currently consumes
  (`mathlib_identifier` / `target_identifier` / `results_used`), or update the
  Lean codegen handlers to consume `lean_name` and `lean_term`.
- When a theorem must be instantiated, include `lean_term`. Most current
  entries have only `lean_name`, so Lean has no term such as
  `map_zpow f g n` to use directly.

### 5. LeanSearch matches are often semantically weak

Some `lean_name` values in the JSON are theorem-like and plausible, but others
look like declarations, classes, namespaces, or unrelated results:

- `GroupSeminorm`
- `Abelianization`
- `Subspace`
- `Dense`
- `instAntisymmLe`
- `Mathlib.Meta.Positivity.int_natAbs_pos`
- `LinearMap.term_∘ₛₗ_`

These names are unlikely to be directly usable as proof terms for the assertion
where they appear. This is a Python-stage ranking/validation problem: the first
LeanSearch result is being accepted as a proof dependency without checking kind,
type compatibility, or whether it can be applied to the local goal.

Recommended Python-side improvement:

- Prefer theorem/lemma declarations over structures/classes/namespaces.
- Keep several LeanSearch candidates when uncertain.
- Include the LeanSearch result type in JSON.
- Do not fill `lean_name` when the match is merely topical.

## Lean Stage Issues

### 1. `defCode` fallback turns definition failure into theorem automation

In `LeanAideCore/LeanAideCore/PaperCodes.lean`, `defCode` first calls
`translator.translateDefCmdM?`. On failure it builds:

```lean
There exists <name> such that:
<statement>
```

then calls `translateToPropStrict` and `findTacticsI` to prove the resulting
proposition.

This is exactly what happened for `commutatorSubgroup`, and it produced a hard
global theorem:

```lean
∀ (G : Type u_1) [inst : Group G],
  commutator G = Subgroup.closure (commutatorSet G)
```

That theorem is not a definition of `commutatorSubgroup`; it is a theorem about
other constants. If those constants do not exist or are not the intended local
definitions, the generated code is structurally wrong even if automation later
finds a proof.

Recommended Lean-side improvement:

- For `definition`, fail with an explicit diagnostic if no definition command
  can be produced.
- If an existential fallback is retained, guard it behind an option and do not
  run heavy automation by default.

### 2. `findTactics?` includes unbounded `try?`

`LeanAideCore/LeanAideCore/CodegenCore.lean` defines automation roughly as:

```lean
runTacticsAndFindTryThis? goal
  ([simp?, grind?, try?, grindWs, simpWs, try simp; exact?] ++ autoTactics)
  (strict := true)
```

The interrupted log stops at:

```lean
example : ... := by try?
```

So the immediate Lean-stage defect is that `try?` can be launched on a hard
global theorem with no timeout/heartbeat cap visible in the codegen wrapper.

Recommended Lean-side improvement:

- Remove `try?` from default codegen automation, or put it behind a strict
  timeout/heartbeat limit.
- Try cheap exact/assumption/simp forms first and stop after bounded failures.
- Log elapsed time per tactic probe.

### 3. Automation runs before using structured proof sources

`getCodeTactics` first calls `findTactics?` on the whole goal. Only if
automation fails does it process the JSON proof sources. This means a large
structured proof can be ignored while Lean tries broad global automation.

For this run the stall is in `defCode`, not in a theorem proof, but the same
pattern will affect the 49 generated theorems once the definition stage is
passed.

Recommended Lean-side improvement:

- For theorem proofs with structured JSON, process the supplied proof steps
  before launching broad automation on the whole goal.
- Use automation as a local fallback after applying a proof step, not as the
  first global attempt.

### 4. `deduced_from_*` fields are not integrated with codegen

`PaperCodes.lean` contains `getResultUsed?` for `results_used`, but the JSON
uses fields named `deduced_from_theorem` and `deduced_from_claim` inside
assertions. Without a handler that turns those fields into `exact`, `apply`,
`have`, or `specialize` terms, they are effectively comments for Lean codegen.

Recommended Lean-side improvement:

- Add `assert_statement` support that reads:
  - `deduced_from_theorem[*].lean_term`,
  - `deduced_from_theorem[*].lean_name`,
  - inserted `specialize` steps,
  - local theorem labels/names.
- If only `lean_name` is present, use it conservatively as a candidate for
  `exact?`/`apply?`, not as a guaranteed proof term.

### 5. Core and non-core `PaperCodes.lean` are not aligned

`LeanAideCore/LeanAideCore/PaperCodes.lean` contains newer handlers such as
`specialize`, while `LeanAide/PaperCodes.lean` appears to be an older or thinner
version. The log uses `LeanAide.defCode`, but the root-cause code path is in
the core module. Divergence between these files makes it easy for a JSON feature
added for the Python pipeline to be supported in one stage and ignored in
another.

Recommended Lean-side improvement:

- Consolidate the handlers or make `LeanAide/PaperCodes.lean` delegate to the
  core implementation consistently.
- Add a small schema compatibility test for every JSON `type` emitted by
  `mathdoc_agent`.

## Expected Next Failures After the Stall Is Removed

If `try?` is removed or bounded, the current JSON is still likely to fail later:

1. The `commutatorSubgroup` definition may fail because it references
   `commutator` and `commutatorSet` rather than the generated
   `commutatorElement` and a generated subgroup definition.
2. `abelianization` depends on `[G,G]`, `G_ab`, and `pi_ab`, but the previous
   subgroup definition has not created stable Lean constants for those.
3. The proof steps contain many `deduced_from_theorem` entries whose `lean_name`
   is not a directly applicable theorem, and most lack `lean_term`.
4. Local claims in `deduced_from_claim` often remain prose strings. Unless they
   have been introduced as named Lean hypotheses, they cannot be used directly.
5. One generated proof is `opaque` in the JSON, so any theorem relying on that
   subproof will need a fallback such as `sorry`, an explicit admitted theorem,
   or a repaired proof object.

## Concrete Fix Order

1. Lean: remove or bound `try?` in `findTactics?`.
2. Lean: make `definition` fail cleanly instead of proving existential fallback
   theorems by heavy automation.
3. Python: generate explicit Lean-facing definitions for the eight introductory
   definitions, with stable names and reference updates.
4. Python/Lean interface: agree on one dependency schema. Either map
   `lean_name` to `mathlib_identifier`/`results_used`, or update Lean codegen to
   consume `lean_name` and `lean_term`.
5. Python: validate LeanSearch results by declaration kind/type before writing
   `lean_name`.
6. Python: generate deterministic theorem names for all 49 top-level theorem
   objects.

## Update: Python-Side Fixes Applied (2026-05-26)

The Python pipeline has been updated and rerun with actual API calls. Lean was
not run.

Implemented fixes:

- Added LeanSearch-backed Mathlib definition reuse before export. If a
  generated definition is conservatively matched to an existing Mathlib
  declaration, the exporter emits a `check` entry instead of duplicating the
  definition.
- Added `lean_name`, `mathlib_kind`, and `mathlib_type` fields to definition
  payloads so Mathlib reuse is recorded internally.
- Made theorem dependency export preserve the original
  `deduced_from_theorem` objects while also emitting `results_used` entries for
  Lean-facing Mathlib names.
- Filtered LeanSearch theorem enrichment to theorem/lemma-like results and
  rejected obvious unusable names such as `noConfusion` declarations and
  generated instance names.
- Added deterministic Lean-style names for exported top-level theorem objects
  and proof-level claim theorem objects.
- Made proof classifier parsing robust to an API response where `notes` is a
  single string instead of an array.
- Increased the default agent timeout to 600 seconds; the homogeneous example
  contains nested construction/existence refinements that exceeded 300 seconds
  in a live pass.

The conservative Mathlib definition reuse deliberately avoids matching the
paper's custom `PseudoLength`, `IsLength`, and
`IsHomogeneousPseudoLength` definitions to unrelated metric or seminorm
structures. It also avoids using the Mathlib subgroup commutator declaration
for the paper's element-level commutator definition.

## Update: Diagnostic Rerun Before Final Patch (2026-05-26)

Command:

```text
./venv/bin/python -m mathdoc_agent.pipeline results/homogeneous.md --id homogeneous -o results/homogeneous.json
```

Observed Python-side failures:

- `homogeneous.root.lemma-5.proof.root`: classifier response had `notes` as a
  string, causing Pydantic validation failure.
- `homogeneous.root.proposition-7.proof.root`: same `notes` validation failure.
- `homogeneous.root.corollary-15.proof.root.reverse.basis-and-norm.choose-basis`:
  structured existence refiner timed out after 300 seconds.

These were fixed by the classifier `notes` coercion and the larger timeout.

## Update: Final Pipeline Rerun After Fixes (2026-05-26)

Command:

```text
./venv/bin/python -m mathdoc_agent.pipeline results/homogeneous.md --id homogeneous -o results/homogeneous.json
```

Final JSON analysis:

- JSON parsed successfully.
- Statuses: `resolved`: 100; no `opaque` nodes.
- Theorem objects: 56 total; 0 missing `name`.
- Top-level theorem names: `lemma_1`, `lemma_2`, `lemma_3`, `lemma_4`,
  `lemma_5`, `lemma_6`, `proposition_7`, `lemma_8`, `lemma_9`, `lemma_10`,
  `lemma_11`, `lemma_12`, `lemma_13`, `theorem_14`, `corollary_15`.
- Reused Mathlib definitions emitted as checks: `commutator`,
  `Abelianization`, `AddCommGroup.torsion`.
- Local definitions still emitted: `PseudoLength`, `IsLength`,
  `IsHomogeneousPseudoLength`, `commutator`, `IsTorsionFreeAbelian`.
- Dependency entries: 108 steps with `deduced_from_theorem`; 9 steps with
  generated `results_used` entries.
- LeanSearch-enriched theorem names no longer include detected `noConfusion`
  declarations or generated instance names.

The final generated JSON still depends on Lean-side support for structured
dependencies. In particular, `deduced_from_theorem` and `deduced_from_claim`
remain useful Python-side information, but Lean codegen must consume
`results_used`, `lean_name`, `lean_term`, local theorem names, and `specialize`
steps to turn them into proof terms. This run did not test that stage because
Lean was intentionally not run.

## Update: Codegen Run With `try?` Disabled (2026-05-26)

Server access was checked before running codegen:

```text
POST http://localhost:7654 {"task": "echo"}
```

The Python client received `result: "success"` with the echoed payload. The
server path used by Python is therefore working, not just shell `curl`.

I then ran:

```text
lake exe codegen results/homogeneous.json
```

The first sandboxed attempt hit network/DNS failures when LeanAide tried to use
OpenAI and similarity search. I stopped that attempt and reran codegen with
server/network permission. The rerun made real OpenAI calls using the
environment, and the log shows `gpt-5.5-2026-04-23` responses and cache writes.

The run did not reach a complete generated Lean file. I stopped it after the
same pattern was diagnosed twice, to avoid spending more API calls on a known
bad path.

Observed Lean-stage behavior:

- `try?` is no longer the immediate stall, but other broad tactics remain:
  `grind?`, generated `grind?` variants, `llm?`, and `hammer`.
- `checkCode` works for Mathlib declarations such as `commutatorElement`,
  `commutator`, `Abelianization`, `AddCommGroup.torsion`, and
  `IsAddTorsionFree`.
- `defCode` still ignores the JSON `name` when translating local definitions.
  It generated names such as `PseudoLengthFunction` and
  `PseudoLengthFunction.IsHomogeneous` rather than the requested `PseudoLength`
  and `IsHomogeneousPseudoLength`.
- When a definition translation fails, `defCode` still falls back to an
  existential theorem of the form `There exists <name> such that: ...` and then
  launches automation. This turned the commutator-subgroup definition into the
  theorem `∀ G [Group G], commutator G = Subgroup.closure (commutatorSet G)`,
  then tried heavy tactics on it.
- The theorem translator still rediscovered theorem statements from prose. In
  the first theorem it changed the homogeneity hypothesis to a natural-number
  version in the generated target, losing the intended integer homogeneity.
- The proof stage tries global automation on whole goals before using the
  structured proof sources from JSON.

Lean-side fixes still needed in `LeanAideCore/LeanAideCore/PaperCodes.lean` and
the corresponding `LeanAide/PaperCodes.lean` path:

- Make definition translation respect the JSON `name`, or reject translations
  whose generated command introduces a different declaration name.
- Remove the existential-theorem fallback for failed definitions, or put it
  behind an explicit option with strict heartbeat/time limits.
- Bound or remove broad default automation probes (`grind?`, generated
  `grind?` variants, `llm?`, `hammer`) in codegen. `try?` was not the only
  unbounded path.
- Use structured proof sources before whole-goal automation, especially
  `results_used`, `deduced_from_theorem[*].lean_name`,
  `deduced_from_theorem[*].lean_term`, local theorem names, and `specialize`
  steps.
- Preserve the formal content of generated theorem statements; do not replace
  integer homogeneity by a weaker or different natural-number hypothesis.
- Configure `LeanAideUrl` or quiet the repeated similarity-search fallback
  diagnostic when the local fallback is expected.

Python-side defects found from this codegen run:

- The element commutator was sometimes emitted as a fresh local definition even
  though Mathlib has `commutatorElement`.
- The subgroup commutator was sometimes emitted as a fresh local definition
  even though Mathlib has `commutator`.
- The abelianization was not robustly reused when LeanSearch failed or when the
  prose used `[G,G]` rather than the word "commutator".
- The torsion subgroup and torsion-free abelian predicate needed deterministic
  reuse of `AddCommGroup.torsion` and `IsAddTorsionFree`.

## Update: Python Fixes After Codegen (2026-05-26)

Implemented in `mathdoc_agent/orchestration/mathlib_reuse.py`:

- Added narrow deterministic Mathlib reuse rules for:
  `commutatorElement`, `commutator`, `Abelianization`,
  `AddCommGroup.torsion`, and `IsAddTorsionFree`.
- Kept the general LeanSearch-backed definition lookup for other definitions.
  During these runs LeanSearch repeatedly returned HTTP 500 for both theorem
  and definition queries, so these specific rules are needed for robustness.

Verification:

```text
./venv/bin/python -m py_compile mathdoc_agent/orchestration/mathlib_reuse.py
./venv/bin/python -m mathdoc_agent.pipeline results/homogeneous.md --id homogeneous -o results/homogeneous.json
```

The pipeline completed with actual API calls. `pytest` was not available in the
venv, so the focused pytest suite could not be run.

Final JSON analysis after the last rerun:

- JSON parsed successfully.
- Statuses: `resolved`: 84; no `opaque` nodes.
- Top-level theorem objects: 15, named `lemma_1` through `corollary_15`.
- Total theorem objects: 44; 0 missing `name`.
- Reused Mathlib declarations emitted as checks:
  `commutatorElement`, `commutator`, `Abelianization`,
  `AddCommGroup.torsion`, `IsAddTorsionFree`.
- Local definitions still emitted:
  `PseudoLength`, `IsLength`, `IsHomogeneousPseudoLength`.
- Dependency entries: 110 steps with `deduced_from_theorem`.
- `results_used` entries: 0 in this final run because LeanSearch returned HTTP
  500 for theorem lookups throughout the run.
- No detected unusable LeanSearch names such as `noConfusion` declarations or
  generated instance names were emitted.

Remaining Python limitation:

- The pipeline currently treats LeanSearch HTTP 500s as soft failures and
  continues. That is correct for completing the run, but it means theorem
  dependencies may lack `lean_name`/`lean_term` until LeanSearch is healthy or a
  separate fallback source is added.

The current Python-side definition reuse defects exposed by codegen are fixed.
The next failures are expected to be Lean-stage issues in definition naming,
definition fallback, theorem statement translation, and proof automation.
