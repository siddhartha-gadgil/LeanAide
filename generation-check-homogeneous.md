# Generation check for `results/homogeneous.md`

## Update: July 4-5 codegen run from `results/homogeneous.json`

Run under diagnosis:

```bash
lake env .lake/build/bin/codegen results/homogeneous.json
```

The run was interrupted after many hours. I did not rerun Lean/codegen for this
audit; the diagnosis below is from `.logs/2026-07-04.log`,
`.logs/2026-07-05.log`, `LeanAideCore/LeanAideCore/PaperCodes.lean`, and
`LeanAide/PaperCodes.lean`.

The logs contain about 152k elaboration records with `cmdErrors`, about 531k
individual command-error entries, and only 13 source-level
`Error in processing source for command` events. The large error count is
therefore mostly repeated elaboration of later prompts/checks in a poisoned
command context, not 531k independent JSON defects. The strongest evidence is
that the same earlier invalid theorem and skipped-command markers appear in the
frontend input for later unrelated translations.

Representative repeated prelude fragment:

```lean
theorem is_length_of_pos_of_ne_one : {G : Type u} → [Group G] → (G → ℝ) → Prop := by
  intro G
  intro inst
  intro f
  exact True
#eval "command skipped due to error in processing source"
#eval "command skipped due to error in processing source"
```

Representative repeated `cmdElabError`:

```text
type of theorem 'is_length_of_pos_of_ne_one' is not a proposition
  {G : Type u} → [Group G] → (G → ℝ) → Prop
```

This invalid command explains a large fraction of the later noise: every later
frontend check that includes the accumulated prelude can fail before reaching,
or independently of, the command currently being translated.

### Root cause of `is_length_of_pos_of_ne_one`

The fallback theorem `is_length_of_pos_of_ne_one` was caused by the translation
of `Definition 2` in `results/homogeneous.json`, not by the homogeneous
definition itself. The JSON entry is:

```json
{
  "type": "definition",
  "label": "Definition 2",
  "definition": "Let G be a group with identity element e. A pseudo-length function l : G → ℝ is a length function if, for every g ∈ G, g ≠ e implies 0 < l(g).",
  "name": "IsLength"
}
```

The LLM did produce the right kind of command for this entry:

```lean
def IsLength {G : Type u} [Group G] (l : G → ℝ) : Prop :=
  IsPseudoLengthFunction l ∧ ∀ g : G, g ≠ 1 → 0 < l g
```

and also produced variants named `IsLengthFunction`. The failure was in the
validation path, not in the first translation. The frontend cache used for this
candidate, `.leanaide_cache/frontend/14394085108435377132_v4.28.0.json`,
contains:

```text
Unknown identifier `IsPseudoLengthFunction`
```

That error is spurious for this codegen run: `IsPseudoLengthFunction` had been
generated immediately before and was available in the translation environment.
The mismatch comes from the Lean validation entry point. In
`LeanAideCore/LeanAideCore/Translate.lean`, `translateDefCmdM?` checks each
candidate by calling:

```lean
let check <- checkElabFrontM (← withCommandPrelude s)
```

`withCommandPrelude` uses `cmdPreludeForFrontendBlob?`, which filters commands
through `commandNeededForFrontendPrelude` in
`LeanAideCore/LeanAideCore/TranslateM.lean`:

```lean
match ← DefData.ofSyntax? cmd with
| some dfn => return (← getEnv).find? dfn.name |>.isNone
| none => return true
```

This drops local generated definitions when they are already present in the
current Meta environment. That can be needed to avoid duplicate declarations,
because `runFrontendM` in `LeanAideCore/LeanAideCore/SimpleFrontend.lean` starts
from the current environment. However, `checkElabFrontM` calls
`runFrontEndForMessages`, whose cache key depends on the input string and Lean
toolchain, not on the current generated environment. The filtered input is
therefore environment-sensitive but cached as if it were environment-independent.
In this run the frontend read the cached result for the reduced input and
rejected the good `IsLength` candidate with `Unknown identifier
IsPseudoLengthFunction`.

After that false rejection, `LeanAideCore/LeanAideCore/PaperCodes.lean` took the
definition fallback path in `defCode`: it translated the prose
`There exists IsLength such that: ...` as a proposition, extracted only the
predicate type

```lean
{G : Type u} → [Group G] → (G → ℝ) → Prop
```

and then emitted:

```lean
theorem is_length_of_pos_of_ne_one :
    {G : Type u} → [Group G] → (G → ℝ) → Prop := by
  intro G
  intro inst
  intro f
  exact True
```

This is invalid because a theorem declaration must have a target of type
`Prop`, whereas the displayed target is a predicate/type shape. Once this bad
theorem entered the accumulated command prelude, it poisoned the next definition
(`IsHomogeneousPseudoLength`) and many later checks. The logs show the bad
theorem included in the prompt prelude for Definition 3, followed by frontend
failures whose first error is again:

```text
type of theorem `is_length_of_pos_of_ne_one` is not a proposition
  {G : Type u} → [Group G] → (G → ℝ) → Prop
```

There are secondary issues in the homogeneous candidates, especially around
integer powers (`g ^ n` with `n : ℤ`) and checking proposition fragments without
their full binder context. Those are real generalization problems, but they are
not the first cause of this fallback chain. The first fix is to make frontend
validation use a coherent context/cache policy. Either check from a fixed base
environment with the full generated textual prelude, or check from the current
environment and include a generated-environment fingerprint in the frontend
cache key. The second fix is to remove or sharply restrict the
definition-to-theorem fallback: failed predicate/type-valued definitions must not
be converted into existential theorem declarations.

Precise changes needed:

1. In `LeanAideCore/LeanAideCore/TranslateM.lean`, decide whether frontend
   validation is environment-relative or text-standalone. The problematic code is
   `commandNeededForFrontendPrelude`. If checks are environment-relative, keep a
   duplicate-declaration filter but make the frontend cache key include a
   fingerprint of the current generated environment or command prelude. If
   checks are text-standalone, remove this filter for
   `cmdPreludeForFrontendBlob?`, run from a fixed base environment, and include
   all accumulated generated commands textually.

2. In `LeanAideCore/LeanAideCore/Translate.lean`, keep
   `translateDefCmdM?` validation and prompt context aligned: the string passed
   to `checkElabFrontM (← withCommandPrelude s)` must contain every local
   generated definition/theorem that the LLM saw in the prompt. If a reduced
   prelude is kept for duplicate-declaration avoidance, do not reuse cached
   frontend results unless the cache key records the environment/prelude on which
   the reduced input depends.

3. In `LeanAideCore/LeanAideCore/PaperCodes.lean` and
   `LeanAide/PaperCodes.lean`, restrict `defCode` fallback. When a JSON
   `"definition"` fails to translate as a command, do not convert it into a
   theorem unless the extracted target is actually a proposition of type `Prop`
   and the source was explicitly an existence claim. Predicate declarations of
   shape `... → Prop`, structures, type-valued definitions, and abbreviations
   should remain definitions or be reported as definition-generation failures.

4. Before any command is added to `cmdPrelude`, check that the full command
   sequence elaborates without frontend errors. Do not add skipped-command
   markers, failed theorem fallbacks, `#eval` failure markers, or `#check`
   diagnostics to the accumulated prelude used for later prompts/checks.

### Main failure mechanisms

1. **Predicate definitions are still falling through to theorem fallback.**

   The bad command above is not a valid theorem because its declared type is a
   function returning `Prop`, not a proposition. It is exactly the shape expected
   for a predicate definition such as:

   ```lean
   def IsHomogeneousPseudoLength {G : Type u} [Group G] (l : G → ℝ) : Prop := ...
   ```

   `LeanAideCore/LeanAideCore/PaperCodes.lean` translates JSON `"definition"`
   entries by calling `translateDefCmdM?`; if that fails, `defCode` builds an
   existential prose claim, translates it with `translateToPropStrict`, asks
   automation for a proof, and emits a theorem. That fallback is too broad for
   mathematical predicates and type-valued definitions. When the original object
   is a definition whose target is `Prop`, the result must remain a `def` or
   `abbrev`, not become a theorem with type
   `{G} → [Group G] → (G → ℝ) → Prop`.

   General fix: make definition generation preserve the definition/proposition
   boundary. If a translated definition candidate has type `... → Prop` or
   `Prop`, emit it as a renamed `def`/`abbrev` with the requested JSON name. Use
   the existential theorem fallback only for objects that are explicitly
   existence claims, not for failed definitions.

2. **Failed/generated placeholder commands are added to the command prelude.**

   `LeanAideCore/LeanAideCore/CodegenCore.lean` catches a source-processing
   exception and returns:

   ```lean
   #eval "command skipped due to error in processing source"
   ```

   The same function then calls `Translate.addCommands code` on every returned
   command sequence. `Translate.addCommands` elaborates and appends those
   commands to `cmdPrelude`. Consequently, skipped-command markers become part
   of later prompt/context blobs. Worse, if a bad command has already been added
   to `cmdPrelude`, `cmdPreludeForFrontendBlob?` and `cmdPreludeBriefBlob?` can
   carry it into every subsequent frontend elaboration and LLM prompt.

   General fix: only successful, semantically useful commands should enter the
   accumulated prelude. Keep skipped-command placeholders out of `cmdPrelude`,
   or stop emitting them as commands at all and record the failure separately.
   `addCommands` should append a command only if frontend elaboration succeeds
   for that command; failed commands must not be retained for future prompts.

3. **Some natural-language hypotheses are not converted into Lean binders or
   local definitions before claims use them.**

   Several later candidate statements contain free symbols such as `f`, `x`,
   `y`, `c`, `ε`, `S2n`, `s`, or `a`. For example, one failed candidate had a
   theorem statement involving:

   ```lean
   f 0 (n : ℤ) ≤ ...
   ```

   while `f` appeared only in prose context such as
   `f(m,k)=l(x^m c^k)`. The result is an elaboration failure for an unknown
   identifier, or a stuck typeclass/metavariable problem caused by missing
   types.

   General fix: the Python stage should turn notation-introducing prose into
   structured `let_statement` objects with explicit Lean values, for example
   `f : ℤ → ℤ → ℝ := fun m k => l (x ^ m * c ^ k)`, and should introduce
   typed binders for all variables used by the claim. On the Lean side,
   candidate theorem/assertion translations should be rejected and repaired if
   they contain identifiers that are neither locally bound nor known
   declarations.

4. **Group power and commutator notation is still under-specified.**

   Common `cmdElabError` lines include:

   ```text
   failed to synthesize instance of type class
     HPow G ℤ ?m.8
   ```

   and stuck multiplication/inverse problems for terms like
   `x * y * x⁻¹ * y⁻¹` when the generated candidate has not made the group
   variables and their types explicit. This is not a LeanSearch problem; it is
   a formalization-context problem. The translator must consistently choose the
   intended algebraic notation, the exponent type, and the group context before
   generating statements that use `g ^ n`, commutators, or iterated powers.

   General fix: generated JSON should carry exact Lean terms for recurring
   local definitions such as commutators and functions of powers, and prompts
   should require the LLM to reuse those terms rather than re-invent notation.
   The Lean checker should reject candidates with unresolved `HPow`, `HMul`, or
   inverse metavariables before proof generation.

5. **Some translated claims are terms rather than propositions.**

   Repeated `Type mismatch` entries show candidate theorem targets ending in an
   `ℝ` expression rather than a proposition, for example a generated target
   ending after:

   ```lean
   ... + ↑n * (l y + l z)
   ```

   with no comparison. This is a statement-translation defect: the theorem
   command parser accepts the syntax shape, but elaboration correctly rejects it
   because theorem targets must be propositions.

   General fix: `translateToPropStrictAux` should continue enforcing that
   accepted theorem/assertion candidates elaborate to `Prop`, but it should also
   feed the proposition/term distinction into the repair prompt. For
   definitions, the analogous check should be different: definitions may have
   type `Prop`, `Type`, or a value type, but they should not be converted into
   theorem declarations unless the JSON object is actually a theorem.

6. **The probability section lacks enough formal context.**

   The July 5 log contains failures and timeouts involving missing probability
   and measure-theory structure, including missing `MeasurableSpace Ω`,
   `MeasureTheory.ae` implicit arguments, `Pairwise` implicit type inference,
   and max-heartbeat failures in `whnf`/`isDefEq`. These arise when prose about
   random signs, expectations, and sums is translated directly to Lean without
   explicitly fixing the probability space, random variables, measurability,
   integrability, and finite-index conventions.

   General fix: Python should emit an explicit formal local context for
   probability lemmas before the Lean translation step. If the source text only
   sketches a probabilistic estimate, the generated theorem should either carry
   the full required hypotheses or be split into smaller named lemmas whose
   assumptions are formal and local.

7. **Direct executable invocation can bypass rebuilding.**

   The command used the already-built executable:

   ```bash
   lake env .lake/build/bin/codegen results/homogeneous.json
   ```

   The binary timestamp is newer than the active `PaperCodes.lean` files in
   this checkout, so this run probably did include the recent fixes. Still,
   this command does not rebuild before running. For future diagnostics, prefer:

   ```bash
   lake exe codegen results/homogeneous.json
   ```

   or explicitly rebuild before using `.lake/build/bin/codegen`, so the source
   under `LeanAideCore/LeanAideCore/PaperCodes.lean` and `LeanAide/PaperCodes.lean`
   is guaranteed to match the executable.

### Code locations implicated

- `LeanAideCore/LeanAideCore/PaperCodes.lean`: `defCode` is the source of the
  over-broad existential theorem fallback for failed definitions.
- `LeanAideCore/LeanAideCore/PaperCodes.lean`: `Translator.translateToPropStrictAux`
  accepts only proposition-like theorem/assertion translations, but its LLM
  repair loop is affected by invalid accumulated preludes.
- `LeanAideCore/LeanAideCore/CodegenCore.lean`: `getCodeCommands` emits skipped
  placeholders and then adds returned commands to the prelude.
- `LeanAideCore/LeanAideCore/TranslateM.lean`: `addCommands`,
  `cmdPreludeForFrontendBlob?`, and `cmdPreludeBriefBlob?` currently have no
  guard against propagating failed or diagnostic commands.
- `LeanAide/PaperCodes.lean`: the theorem wrapper follows the same
  `translateToPropStrict` path, so its theorem/proof translation is vulnerable
  to the same poisoned context and missing-binder failures.

### Recommended fixes

1. Change definition codegen so predicate/type-valued definitions remain
   definitions. Remove or sharply restrict the existential fallback in
   `defCode`; it should not run merely because `translateDefCmdM?` failed for a
   JSON object of type `"definition"`.

2. Change command accumulation so only successfully elaborated user-visible
   declarations are added to `cmdPrelude`. Do not add
   `#eval "command skipped due to error in processing source"` or any failed
   command to the prelude used for frontend checks or prompts.

3. When checking a new candidate from the LLM, separate errors caused by the
   current candidate from errors caused by previous prelude commands. A clean
   successful-prelude-only environment should be used for candidate elaboration.

4. Add a Lean-side candidate rejection pass for unbound identifiers and stuck
   algebraic typeclass metavariables before proof search. The repair prompt
   should explicitly ask for missing binders/local definitions or reuse of the
   existing local context.

5. Strengthen Python JSON generation for local notation: every notation
   introduced in prose and used later should become a typed `let_statement`,
   `assume_statement`, or named lemma with a Lean term. This is especially
   important for `f(m,k)`, commutators, quotient representatives, probabilistic
   random variables, and aggregate variables such as `S2n`.

6. For probability/measure-theory sections, generate the formal probability
   context first and force all subsequent statements to reuse that context.
   Missing measure-space, measurability, integrability, and finite-index
   assumptions should be Python-side generation errors, not left to codegen.

## Run

Command run, without `--lean`:

```bash
./venv/bin/python -m mathdoc_agent.pipeline \
  results/homogeneous.md \
  --id homogeneous \
  -o results/homogeneous.json
```

The command used the live OpenAI agent path with `OPENAI_API_KEY` present in the
environment. No fake agents were used. I did not run Lean or the pipeline
`--lean` path.

Generated file:

```text
results/homogeneous.json
```

The generated JSON is syntactically valid. Top-level structural counts in the
output:

- `definition`: 8
- `theorem`: 49, including nested local theorem nodes
- `proof`: 57
- `assert_statement`: 192
- `let_statement`: 37
- `assume_statement`: 15
- `construction_proof`: 8
- `existence_proof`: 1
- `induction_proof`: 1
- `bi-implication_cases_proof`: 1
- objects still containing `deduced_from_claim`: 83
- `specialize` steps inserted by the final rewrite pass: 0
- opaque proof nodes: 1

## Python-Side Findings

1. **Initial run hung in a live calculation-agent call.**

   The first real run stalled for several minutes at:

   ```text
   homogeneous.root.lemma-2.proof.root.base-n-0
   ```

   The Python runner had no per-agent timeout, so one slow or stuck live API call
   could block the whole pipeline indefinitely.

   Fix applied: `mathdoc_agent/mathagents/runner.py` now wraps live agent calls in
   `asyncio.wait_for`, with default timeout `180` seconds and optional override
   by `MATHDOC_AGENT_AGENT_TIMEOUT_SECONDS`. The proof orchestrator already
   catches handler exceptions and marks only the failed proof node opaque, so the
   pipeline can continue.

2. **Rerun completed, with one timeout converted to an opaque subproof.**

   The rerun completed and wrote `results/homogeneous.json`. One calculation
   subproof timed out after the new 180 second bound:

   ```text
   homogeneous.root.lemma13.proof.root.real_scalar_multiplication.independence
   ```

   In the JSON this appears as one `status: "opaque"` node at:

   ```text
   /document/body/29/proof/verification/proof_steps/4/verification/proof_steps/4
   ```

   This is now a controlled Python-side degradation instead of a pipeline hang.

3. **The `deduced_from_claim` rewrite pass ran but left many dependencies.**

   The final `Deduced-from-claim rewriter` agent ran successfully, followed by the
   claim auditor. However, 83 objects still contain `deduced_from_claim`. These
   are mostly local algebraic dependencies such as:

   ```text
   z = y * x * y^{-1}
   l(x^n) = n * l(x)
   f(r,s)=l(x^r c^s)
   ```

   PaperCodes does not consume `deduced_from_claim` directly, so these remaining
   fields are metadata rather than proof instructions. This is not a Python
   exception, but it is a codegen risk: if those dependencies are actually needed
   to prove an assertion, they should become explicit prior `assert_statement`,
   `specialize`, or local `theorem` steps.

## PaperCodes-Facing Risks

1. **Definitions are still natural-language commands.**

   The output now has Lean-style definition names such as `PseudoLength`,
   `IsHomogeneousPseudoLength`, `commutator`, `commutatorSubgroup`,
   `abelianization`, and `torsionSubgroup`. This is better than the earlier prose
   names.

   The `definition` strings are still prose, for example:

   ```text
   Let G be a group ... A function l : G -> R is a pseudo-length function ...
   ```

   `LeanAideCore/LeanAideCore/PaperCodes.lean` handles `definition` by sending
   the string to `translateDefCmdM?`, and on failure tries a proposition
   `There exists {name} such that ...` using `translateToPropStrict`. Both paths
   may fail or generate noncanonical Lean declarations for these mathematical
   structure definitions.

2. **Most theorem and assertion claims still rely on translation from prose.**

   `assert_statement` in `LeanAideCore/LeanAideCore/PaperCodes.lean` ignores
   `deduced_from_claim` and `deduced_from_theorem`; it only translates the
   `claim` field and then calls automation. This affects 192 generated
   `assert_statement` objects.

   Examples likely to be difficult:

   ```text
   f(0,n) <= the expectation of f(M_{2n}, K_{2n})
   E(S2n^2) = 2n
   E[f(S_{2n},-S_{2n}/2)] <= E(|S_{2n}|)(l(x)+l(c)/2)
   ```

   The probability/random-variable part remains the highest-risk section.

3. **`deduced_from_theorem` / `lean_name` is not used by `assert_statement`.**

   The generated JSON contains many `deduced_from_theorem` objects with
   `lean_name`, but PaperCodes has a separate `results_used` mechanism via
   `getResultUsed?`, expecting `target_identifier`, `mathlib_identifier`, or
   `statement`.

   Unless another layer maps `deduced_from_theorem` to `results_used`, the Lean
   codegen path will not directly use the LeanSearch names.

4. **`construction_proof` fields are more identifier-like, but constructions are
   still prose.**

   The generated construction variable names are now Lean-style identifiers; no
   bad construction variable names were found by a simple identifier check.

   The construction strings are still not Lean terms:

   ```text
   normQ(a/n) := p(a)/n for a in A and n a positive integer
   completionB := the metric completion of W=VQ/N, where N={v in VQ | normQ(v)=0}
   scalarMul(alpha, b) := lim_i q_i w_i, where ...
   iota := the canonical composite VQ -> VQ/N -> B
   ```

   `LeanAide/PaperCodes.lean` requires `construction_proof` to translate
   `full_claim`, then synthesize an existence proof from `variable_name`,
   `construction`, and `verification`. Long prose constructions are likely to
   fail or produce brittle generated terms.

5. **The new `specialize` codegen hook is available but unused in this output.**

   `LeanAideCore/LeanAideCore/PaperCodes.lean` now has a `specialize` handler
   that emits a non-destructive `have name := lean_term` form. The JSON from this
   run contains no `specialize` steps, so none of the remaining
   `deduced_from_claim` dependencies were converted into explicit instantiations.

6. **One opaque subproof will not provide proof content.**

   The timed-out node under the real scalar multiplication construction is
   exported as `opaque`. Any Lean-side codegen path that expects a proof for that
   nested verification will either need to tolerate opacity or fail when trying
   to use that verification.

## Highest-Risk JSON Locations

- `/document/body/19` and `/document/body/20`: probabilistic lemmas with
  Rademacher variables, expectations, and `S_{2n}` notation.
- `/document/body/21`: proof of commutator vanishing depends on probabilistic
  estimates and expectation bounds.
- `/document/body/28`: construction of `normQ` on `A tensor_Z Q`; fraction
  representation and quotient-style notation are encoded as prose.
- `/document/body/29`: construction of the Banach space completion and real
  scalar multiplication; contains the one opaque timed-out subproof.
- `/document/body/31` and `/document/body/33`: representation theorem and
  converse construction still use norm notation such as `||phi(g)||_B` and
  tensor-space prose.

## Verification Commands

After fixing the Python timeout issue, these checks passed:

```bash
./venv/bin/python -m py_compile mathdoc_agent/mathagents/runner.py
./venv/bin/python -m unittest \
  mathdoc_agent.tests.test_leansearch \
  mathdoc_agent.tests.test_handlers_and_orchestration
./venv/bin/python -m unittest mathdoc_agent.tests.test_pipeline
```

The final pipeline rerun completed successfully without Lean.
