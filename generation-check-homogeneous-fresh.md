# Generation check for `results/homogeneous.md`

## Run

Final command run:

```bash
./venv/bin/python -m mathdoc_agent.pipeline \
  results/homogeneous.md \
  --id homogeneous \
  -o results/homogeneous-fixed2.json
```

The first sandboxed run failed before reaching OpenAI because DNS/network access
was blocked. Subsequent runs were made with network access and used the
`OPENAI_API_KEY` environment variable. No fake agents were used. I did not run
Lean and did not pass `--lean`.

One intermediate run exposed a recursive `generic_element` expansion in Lemma 9;
that run was stopped before completion and the prompt was fixed. A later run
exposed a Python string escape warning in the prompt text; that run was also
stopped and the prompt was corrected before the final run.

Generated file:

```text
results/homogeneous-fixed2.json
```

## Changes made in `mathagents`

Edited:

```text
mathdoc_agent/mathagents/prompts.py
```

The live-agent prompts now require:

- ordinary definitions to populate `data_entries` with Lean-codegen-oriented
  `term` and `definiens` metadata;
- definition names and construction/let variable names to be ASCII
  identifier-shaped;
- construction payloads to be assignment-shaped and one object at a time;
- generic-element proofs not to recursively create another generic-element
  setup component;
- claims to avoid instruction text, local `if C_n := ...` syntax, raw Markdown,
  LaTeX commands, unicode subscripts, and display notation when local
  identifiers are available.

Sanity check run:

```bash
./venv/bin/python -m py_compile mathdoc_agent/mathagents/prompts.py
```

## Final output shape

Top-level generated structure:

- `document`: 1
- `definition`: 8
- `theorem`: 50, including local claim theorems emitted inside proofs
- `proof`: 63
- `assert_statement`: 223
- `let_statement`: 35
- `assume_statement`: 18
- `construction_proof`: 8
- `existence_proof`: 3
- `induction_proof`: 1

## PaperCodes-facing analysis

1. **Definitions are now much better matched to `defCode`.**

   `LeanAideCore/LeanAideCore/PaperCodes.lean` reads `definition` and `name`,
   parses `name` as a Lean `Name`, and sends the definition string to
   `translateDefCmdM?`. The generated definitions now have identifier-shaped
   names:

   - `PseudoLength`
   - `IsLength`
   - `IsHomogeneousPseudoLength`
   - `commutator`
   - `commutatorSubgroup`
   - `abelianization`
   - `torsionSubgroup`
   - `IsTorsionFree`

   The old Markdown headers such as `**Definition 1 ...**` are gone from the
   `definition` payloads. There were no invalid definition names by the final
   scan.

2. **Construction and let variable names are now identifier-shaped.**

   `LeanAide/PaperCodes.lean` handles `construction_proof` by reading
   `variable_name`, applying `mkIdent variableName.toName`, proving an
   existential, and destructuring it. The final JSON had 8 construction proofs
   and no invalid construction/let/assume variable names.

   Representative construction variables:

   - `barL`
   - `normQ`
   - `B`
   - `quotientW`
   - `normW`
   - `completionB`
   - `realScalarMul`
   - `iota`

   This fixes the previous failures involving names like `||·||_Q`, `(B,\iota)`,
   `αb`, and `||·||`.

3. **Construction payloads are improved but still semantically heavy.**

   The final construction fields are assignment-shaped, for example:

   - `barL(pi_ab(g)) := l(g) for g in G`
   - `normQ(a/n) := p(a)/n ...`
   - `quotientW := VQ/N`
   - `normW([v]) := normQ(v)`
   - `iota := the canonical composite VQ -> VQ/N -> B`

   The main Lemma 13 witness still necessarily packages substantial mathematics:
   `B := the metric completion of the normed rational vector space W = VQ/N ...`.
   That is no longer a malformed identifier problem. If codegen later fails
   here, the likely fix is to split the source theorem or the export/codegen
   schema further, not another broad mathagents prompt tweak.

4. **Claim notation is substantially cleaner.**

   Final scan:

   - claims containing `$`: 0
   - claims with unicode subscript characters: 0
   - claims with local-definition syntax like `if C_n := ...`: 0
   - claims with LaTeX commands: 1, only inside a dependency theorem statement
   - claims with display norm notation: 1, only inside a dependency theorem
     statement

   The old theorem statement for Lemma 2 with `if C_n := ...` was eliminated.
   Most display notation was replaced by identifiers such as `barL`, `normQ`,
   and `VQ`.

5. **Probability remains the main unavoidable translation risk.**

   The final JSON still has 16 claim/dependency entries involving expectation or
   Rademacher variables. This is a real mathematical part of Lemmas 5 and 6, not
   just formatting. `translateToPropStrict` may still struggle unless the Lean
   side has a probability setup or the source is rewritten as a finite
   sign-vector average.

6. **References are still not in `results_used`.**

   `LeanAideCore/LeanAideCore/PaperCodes.lean` has `getResultsUsed`, but
   `assert_statement` codegen does not consume `deduced_from_theorem` or
   `deduced_from_claim`; it mainly translates the claim and searches tactics.
   The generated JSON contains:

   - `deduced_from_theorem`: 110
   - `deduced_from_claim`: 165
   - `results_used`: 0

   This is not fixable by the current mathagents prompts alone because the
   public refinement schemas expose `deduced_from_*`, while `results_used` would
   need an exporter/schema mapping or PaperCodes support.

7. **Nested local claims remain, but less severely.**

   The final JSON has 35 theorem nodes inside proof subtrees. PaperCodes can
   generate local `have` statements for theorem nodes in tactic context, but
   broad local theorem statements remain more fragile than direct
   `assert_statement` steps. This count is lower than the earlier rerun but is
   still worth watching if Lean codegen is enabled later.

## Current conclusion

The fixable mathagents generation defects identified from the original report
were addressed and rerun with actual OpenAI API calls:

- definition names and payloads are no longer Markdown/prose-name shaped;
- construction and let variable names are valid identifiers;
- the generic-element recursion defect is fixed;
- claims are much less LaTeX/display-notation-heavy;
- the `if C_n := ...` theorem statement shape is gone.

The remaining risks are mostly outside a prompt-only mathagents fix:

- the probability/Rademacher section needs either a source-level finite
  sign-vector formulation or dedicated Lean probability support;
- dependency references should be mapped to `results_used` in export/codegen, or
  `PaperCodes.lean` should consume the existing `deduced_from_*` fields;
- complex analytic constructions in Lemmas 12 and 13 may need source theorem
  splitting or more specialized codegen support if Lean elaboration is later
  attempted.
