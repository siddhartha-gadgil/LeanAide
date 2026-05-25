# Generation check for `results/homogeneous.md`

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
