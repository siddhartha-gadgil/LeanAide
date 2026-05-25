# Generation check for `results/homogeneous.md`

## Run

Command run:

```bash
PYTHONPYCACHEPREFIX=/private/tmp/leanaide_pycache \
./venv/bin/python -m mathdoc_agent.pipeline \
  results/homogeneous.md \
  --id homogeneous \
  -o results/homogeneous.json
```

The first sandboxed run failed with an OpenAI connection error.  The command was
rerun with network access and used the `OPENAI_API_KEY` environment variable.
No fake agents were used, and I did not run Lean or the `--lean` codegen path.

Generated file:

```text
results/homogeneous.json
```

Top-level generated structure:

- `document`: 1
- `definition`: 8
- `theorem`: 45, including nested local claim theorems
- `proof`: 58
- `assert_statement`: 249
- `let_statement`: 21
- `assume_statement`: 13
- `construction_proof`: 11
- `existence_proof`: 1
- `induction_proof`: 1
- `bi-implication_cases_proof`: 1

## PaperCodes-facing findings

1. **Definitions are likely to translate poorly.**

   The generated `definition` nodes keep Markdown headers and LaTeX, for example
   `**Definition 1 (Pseudo-length function).** ...`.  In
   `LeanAideCore/LeanAideCore/PaperCodes.lean`, `defCode` reads the
   `definition` string and sends it to `translateDefCmdM?`; it also reads
   `name` as a Lean `Name`.  Generated names such as `"Pseudo-length function"`
   and `"Torsion subgroup of an abelian group"` are prose names, not useful Lean
   identifiers.

   Likely improvement: rewrite source definitions with Lean-oriented identifiers
   and no Markdown in the definitional payload, e.g. `PseudoLength`,
   `IsHomogeneousPseudoLength`, `commutator`, `commutatorSubgroup`,
   `abelianization`, `torsionSubgroup`.

2. **`construction_proof` variable names are not Lean identifiers.**

   `LeanAide/PaperCodes.lean` handles `construction_proof` by reading
   `variable_name`, applying `mkIdent variableName.toName`, and destructuring an
   existential proof.  The generated JSON contains names such as:

   - `||·||_Q`
   - `(B,\iota)`
   - `αb`
   - `||·||_1`
   - `||·||`

   These are mathematical display names, not robust Lean identifiers.

   Likely improvement: use identifier-style names in the source text or patch the
   JSON before codegen: `normQ`, `B_iota`, `realSMul`, `normOne`, `basisNorm`.
   For a pair such as `(B,\iota)`, split the construction into nested existential
   steps or introduce a single Lean identifier for the pair.

3. **Construction payloads are prose, not terms.**

   The `construction` field is expected to provide a first-class construction or
   definition.  Several generated constructions are long prose descriptions, for
   example:

   ```text
   Identify A with its image in V_Q and define ||a/n||_Q:=p(a)/n ...
   ```

   and

   ```text
   N={v∈V_Q | ...}, W=V_Q/N, B=completion of W, and iota is ...
   ```

   Likely improvement: make the source separate each object into explicit
   `let`-style definitions with identifier names: define `N`, define `W`, define
   `B`, define `iota`, then prove properties.  This aligns better with
   `let_statement` and `construction_proof`.

4. **Many proof claims use raw LaTeX or unicode notation.**

   There are hundreds of generated claims containing `$...$`, `\mathbb`,
   subscripts such as `S_{2n}`, unicode arrows, `⊗`, `∈`, and norm notation.
   `assert_statement` sends the `claim` string to `translateToPropStrict`; this
   can work, but it forces translation on every small step.

   Likely improvement: avoid display notation in atomic proof steps.  Prefer
   prose-plus-identifiers such as `S twoN`, `eps`, `normQ`, `iota`, and reserve
   LaTeX for the surrounding exposition.

5. **Some theorem claims contain non-Lean local-definition syntax.**

   Lemma 2 was generated with:

   ```text
   For every natural number n, if C_n := ..., then ...
   ```

   This is natural prose but awkward for proposition translation.  Lean would
   prefer either an explicit local function `C : Nat -> G` or the expression
   inlined in the conclusion.

   Likely improvement: state recurrence lemmas using explicit functions:

   ```text
   Define C : Nat -> G by C n = ...
   Then for every n : Nat, ...
   ```

6. **Side conditions became standalone assertions.**

   The JSON contains assertions like `l is a pseudo-length function`,
   `s^{-1},t∈G`, `m>0`, and `n>0`.  `assert_statement` tries to prove each as a
   local `have`, which may create unnecessary translation and automation work.

   Likely improvement: keep side conditions in hypotheses or assumptions, not as
   proof assertions.  Obvious typing facts such as `s^{-1}, t ∈ G` should be
   omitted from the structured proof.

7. **References to previous lemmas are not in the field PaperCodes uses most.**

   Many steps have `deduced_from_theorem`, but `assert_statement` does not use
   that field directly.  `getResultUsed?` is wired to `results_used`, with
   `target_identifier` or `mathlib_identifier`.

   Likely improvement: for generated JSON intended for codegen, prefer
   `results_used` entries with `target_identifier` matching earlier theorem
   labels, for example the conjugation-invariance lemma and splitting lemma.

8. **Probability notation is a major translation risk.**

   Lemmas 5 and 6 use Rademacher random variables and expectations.  The JSON
   preserves notation such as `\mathbb{E}`, `S_{2n}`, and `epsilon_i`.
   Without a dedicated probability setup, `translateToPropStrict` will have to
   invent the Lean representation.

   Likely improvement: either introduce a concrete finite combinatorial average
   over sign vectors, or isolate the probabilistic estimate as a named auxiliary
   theorem with a simpler statement for the codegen stage.

9. **Nested local claims are emitted as `theorem` nodes.**

   PaperCodes can turn a theorem node in a tactic context into a `have`, but
   nested local claims with broad prose statements often lose the surrounding
   variable context during translation.

   Likely improvement: use `assert_statement` for local facts and reserve
   top-level `theorem` nodes for globally reusable lemmas.

## Most useful source edits before another generation

1. Add a short Lean-oriented notation section after the definitions, assigning
   identifier names to all structures/functions used later.

2. Replace display names in constructions with identifiers:
   `normQ`, `N`, `W`, `B`, `iota`, `basis`, `basisNorm`, `lengthFromNorm`.

3. Rewrite Lemma 12 and Lemma 13 as smaller statements:
   one lemma for the fraction seminorm on `A ⊗ ℚ`, one for quotienting by the
   zero seminorm, one for completing a normed rational vector space.

4. Replace the probabilistic random-walk section with a finite sign-vector
   formulation or explicitly state the probabilistic estimate as an external
   auxiliary lemma.

5. In proof text, avoid asserting type side-conditions and avoid local
   definition syntax of the form `if C_n := ...`.  Use `Let C : Nat -> G be ...`
   and refer to `C n`.

These changes should reduce the number of natural-language translation calls in
`assert_statement` and `definition`, and should make the generated JSON better
matched to the handlers in `PaperCodes.lean`.
