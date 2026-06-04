# Codegen report for `homogeneous.json` / `homogeneous.lean`

Date analysed: 2026-06-04.

Inputs used:

- JSON: `results/homogeneous.json`
- generated Lean: `CodeGen/homogeneous.lean`
- codegen log: `.logs/2026-06-04.log` (the requested `.logs/2026-06-04.md` is not present)
- Lean code paths inspected: `LeanAideCore/LeanAideCore/PaperCodes.lean`, `LeanAide/PaperCodes.lean`, `LeanAideCore/LeanAideCore/CodegenCore.lean`, `LeanAideCore/LeanAideCore/Translate.lean`, `LeanAideCore/LeanAideCore/TranslateM.lean`
- Python code paths inspected: `mathdoc_agent/pipeline.py`, `mathdoc_agent/orchestration/deduced_from_claim_rewrite.py`, `mathdoc_agent/orchestration/lean_lint.py`

I did not run Lean while preparing this report.

## Executive summary

The current run is much better structurally than the earlier run: the Lean-facing JSON has no `results_used` key, no `deduced_from_claim` key, no `lean_validation` quarantine metadata, and it includes `source` fields on definitions and theorems. However, the run still fails for three general reasons.

1. Some accepted definitions are semantically wrong. In particular, `IsLength` and `IsHomogeneousPseudoLength` are generated as Prop-valued definitions returning `True`, so later theorems are proved against a meaningless formal context.

2. The theorem and proof-step translation pipeline still loses mathematical hypotheses and local context. Several generated theorem statements are false as stated because assumptions such as "l is a homogeneous pseudo-length function" or the recursive definition of `C` are not part of the theorem statement.

3. The Lean codegen side repeatedly tries to elaborate candidates without the generated declarations available as real Lean context, falls back to subexpressions containing `sorry`, and treats theorem names as if they were already correctly instantiated proof terms.

The generated file has only 15 declarations:

```text
IsPseudoLengthFunction, isLength_of_pos_of_ne_one, is_homogeneous_pseudo_length_sq,
AddCommGroup.TorsionFree, lemma_1, lemma_2, lemma_3, lemma_4, lemma_5, lemma_6,
proposition_7, lemma_8, lemma_9, lemma_10, lemma_13
```

The JSON contains 15 theorem objects, but `lemma_11`, `lemma_12`, `theorem_14`, and `corollary_15` failed at source-command generation and were emitted only as skipped commands.

## Quality change from the previous run

Compared with the previous run, the quality has improved at the schema-hygiene and diagnostic-visibility layers, but not yet at the mathematical/formalization layer.

The clear improvements are:

- The Lean-facing JSON no longer emits the unsupported `results_used` or `deduced_from_claim` keys.
- The output is smaller and easier to inspect: the previous report described an 8,694-line generated file, while this run generated 1,674 lines.
- The generated file has a compact elaboration footer with 31 sorry goals and no `Sorries after purge`, making the remaining proof obligations easier to classify.
- Top-level definitions and theorems now carry `source` data, which is essential for future drift diagnosis.
- Failures are now concentrated in a smaller number of mechanisms: bad definition fallback, missing theorem context, unverified theorem dependencies, and incomplete construction handling.

However, the actual formalization quality has not improved, and in some ways the current failures are more serious because they occur earlier in the dependency chain:

- Two central definitions, `IsLength` and `IsHomogeneousPseudoLength`, collapsed to Prop-valued shells proved by `exact True`.
- Several theorem statements are false as generated because ambient hypotheses were not promoted into Lean assumptions.
- The generated Lean contains more visible proof placeholders than the previous report's raw count: 108 `sorry` tokens and 87 `repeat (sorry)` occurrences in the current file.
- Four theorem objects fail completely at source-command generation (`lemma_11`, `lemma_12`, `theorem_14`, `corollary_15`).
- The JSON has 125 theorem-dependency records but zero instantiated `lean_term` fields, so theorem use remains mostly unverified name citation.

The important assessment is therefore:

```text
Schema cleanup:          improved.
Failure localization:   improved.
Definition correctness: regressed or still broken.
Theorem statement faithfulness: still poor.
Proof completion:       still poor.
Overall formal quality: not yet improved.
```

The logs show why this happened. Around `.logs/2026-06-04.log:300-370`, the LLM proposes a useful `IsLength` definition, but the elaboration path accepts only its type `{G : Type u} -> [Group G] -> (G -> R) -> Prop`; automation then fills the definition with `True`. Around `.logs/2026-06-04.log:560-710`, the same pattern happens for `IsHomogeneousPseudoLength`: the prompt even contains prior code context, but the accepted result is again a type shell rather than the actual definition body. This explains why later theorem translation has a poisoned context.

The Lean-side root is in the definition path in `LeanAideCore/LeanAideCore/PaperCodes.lean`. The `defCode` handler tries `translator.translateDefCmdM?`; if that path fails or yields an unsuitable command, it falls back to translating `"There exists <name> such that: ..."`, then accepts a proposition/type and asks tactics to inhabit it. That fallback is useful for a theorem, but it is unsound as a definition-generation fallback because it loses the definitional body. The handler must distinguish "I have a valid `def` command" from "I have proved there exists something".

The theorem path explains the next quality problem. In `LeanAideCore/LeanAideCore/PaperCodes.lean`, `theoremCodeCore` translates only the theorem's `claim` string, then later runs proof code against the resulting type. If the theorem source has ambient assumptions that are not explicitly represented in the JSON claim or hypothesis fields, they are lost. This is why `lemma_1` becomes a theorem about an arbitrary function `l : G -> R`, and why the proof later tries to recover "l is homogeneous" as a materialized local assertion. The log around `.logs/2026-06-04.log:2630-2710` shows exactly this: translating `"l is homogeneous."` fails, then the path reports no valid function for `assert_statement`.

The assertion path explains why theorem dependencies are not helping enough. In `LeanAideCore/LeanAideCore/PaperCodes.lean`, `assertionCode` treats a `lean_name` as a fallback `lean_term`, parses it as a term, and tries to create a have from it. The log around `.logs/2026-06-04.log:3630-3675` shows the typical failure: `Units.conj_pow` cannot be used directly because the theorem is not instantiated and typeclass inference is stuck at a metavariable. This is not a one-off; the log records 48 failures to create have tactics from theorem names.

The extended codegen layer in `LeanAide/PaperCodes.lean` adds another failure mode for later theorems. Its `letCode` asks the translator to "Define ONLY the term" from prose, and `constructionProofCode` translates `full_claim` before building an existential witness. For simple local variables this can work, but for quotient maps, induced functions, tensor products, and Banach completions it is too underspecified. The source failures for `theorem_14` and `corollary_15` are consequences: the JSON gives prose descriptions of dependent constructions, while the Lean handlers need exact terms, destructuring instructions, and theorem applications.

The dominant elaboration failure class confirms this diagnosis. The log contains 2,092 parsed elaboration error records, including 1,729 unknown-identifier/function-expected records. The main pattern is that prompts show previous generated code, but the frontend candidate checks do not reliably elaborate in that same generated-code context. This is why names such as `IsPseudoLengthFunction`, `isLength_of_pos_of_ne_one`, and `is_homogeneous_pseudo_length_sq` are shown to the LLM yet still fail as unknown identifiers in candidate elaboration. This is a major root cause, not a cosmetic logging issue: it means that translated statements are selected under a different environment from the one described to the model.

## Exact log excerpts supporting the quality assessment

These excerpts are copied verbatim from `.logs/2026-06-04.log`, since the log file is not tracked in git.

### Definition body lost for `IsLength`

The LLM candidate contains the intended body, but the frontend check and subsequent type extraction keep only the function-to-`Prop` type.

```text
[2026-06-04T07:20:11] [leanaide.elaboration.info] Trying to elaborate 'def IsLength {G : Type u} [Group G] (l : G → ℝ) : Prop :=
[2026-06-04T07:20:11] [leanaide.elaboration.info]   IsPseudoLengthFunction l ∧ ∀ g : G, g ≠ 1 → 0 < l g'
[2026-06-04T07:20:11] [leanaide.frontend.info] Running frontend (no cache) on input:
[2026-06-04T07:20:11] [leanaide.frontend.info] example : {G : Type u} → [Group G] → (l : G → ℝ) → Prop := by sorry
[2026-06-04T07:20:11] [leanaide.frontend.info] Running frontend on input:
[2026-06-04T07:20:11] [leanaide.frontend.info] example : {G : Type u} → [Group G] → (l : G → ℝ) → Prop := by sorry
[2026-06-04T07:20:11] [leanaide.frontend.info] Frontend finished with 1 messages
[2026-06-04T07:20:11] [leanaide.frontend.info] Frontend wrote to /Users/gadgil/code/LeanAide/.leanaide_cache/frontend/10967794120872185135_v4.28.0.json with 1 messages
[2026-06-04T07:20:11] [leanaide.frontend.info] Running frontend on input:
[2026-06-04T07:20:11] [leanaide.frontend.info] set_option autoImplicit false in
[2026-06-04T07:20:11] [leanaide.frontend.info] noncomputable def my_shiny_new_theorem : {G : Type u} → [Group G] → (l : G → ℝ) → Prop := by sorry
[2026-06-04T07:20:11] [leanaide.frontend.info] Frontend finished with 1 messages
[2026-06-04T07:20:11] [leanaide.elaboration.info] Succeeded in elaborating 'def IsLength {G : Type u} [Group G] (l : G → ℝ) : Prop :=
[2026-06-04T07:20:11] [leanaide.elaboration.info]   IsPseudoLengthFunction l ∧ ∀ g : G, g ≠ 1 → 0 < l g'
[2026-06-04T07:20:11] [leanaide.papercodes.info] Obtained type: {G : Type u} → [Group G] → (G → ℝ) → Prop
[2026-06-04T07:20:11] [leanaide.papercodes.info] Obtained type in local context: {G : Type u} → [Group G] → (G → ℝ) → Prop
[2026-06-04T07:20:11] [leanaide.codegen.info] Trying automation tactics
[2026-06-04T07:20:11] [leanaide.codegen.info] previous definitions/theorems names: #[]
[2026-06-04T07:20:11] [leanaide.interpreter.info] Running tactics on {G : Type u} → [Group G] → (G → ℝ) → Prop to get messages in context:
[2026-06-04T07:20:11] [leanaide.interpreter.info] LocalHyps: #[]
[2026-06-04T07:20:11] [leanaide.interpreter.info] FVars:
[2026-06-04T07:20:11] [leanaide.interpreter.info] Target type: {G : Type u} → [Group G] → (G → ℝ) → Prop
```

### Definition body lost for `IsHomogeneousPseudoLength`

This shows the same loss, plus the risky "Succeeded on sub-line" fallback.

```text
[2026-06-04T07:22:03] [leanaide.elaboration.info] Trying to elaborate 'def IsHomogeneousPseudoLength {G : Type u} [Group G] (l : G → ℝ) : Prop :=
[2026-06-04T07:22:03] [leanaide.elaboration.info]   IsPseudoLengthFunction l ∧ ∀ (g : G) (n : ℤ), l (g ^ n) = |(n : ℝ)| * l g
[2026-06-04T07:22:03] [leanaide.elaboration.info] 
[2026-06-04T07:22:03] [leanaide.elaboration.info] theorem IsHomogeneousPseudoLength.sq : ∀ {G : Type u} [Group G] {l : G → ℝ},
[2026-06-04T07:22:03] [leanaide.elaboration.info]   IsHomogeneousPseudoLength l → ∀ (g : G), l (g ^ (2 : ℤ)) = 2 * l g := by sorry'
[2026-06-04T07:22:03] [leanaide.elaboration.info] Checking groups: 31
[2026-06-04T07:22:03] [leanaide.frontend.info] Frontend read from /Users/gadgil/code/LeanAide/.leanaide_cache/frontend/10967794120872185135_v4.28.0.json with 1 messages (from cache)
[2026-06-04T07:22:03] [leanaide.frontend.info] Running frontend on input:
[2026-06-04T07:22:03] [leanaide.frontend.info] set_option autoImplicit false in
[2026-06-04T07:22:03] [leanaide.frontend.info] noncomputable def my_shiny_new_theorem : {G : Type u} → [Group G] → (l : G → ℝ) → Prop := by sorry
[2026-06-04T07:22:03] [leanaide.frontend.info] Frontend finished with 1 messages
[2026-06-04T07:22:03] [leanaide.elaboration.info] Succeeded on sub-line for 'def IsHomogeneousPseudoLength {G : Type u} [Group G] (l : G → ℝ) : Prop :=
[2026-06-04T07:22:03] [leanaide.elaboration.info]   IsPseudoLengthFunction l ∧ ∀ (g : G) (n : ℤ), l (g ^ n) = |(n : ℝ)| * l g
[2026-06-04T07:22:03] [leanaide.elaboration.info] 
[2026-06-04T07:22:03] [leanaide.elaboration.info] theorem IsHomogeneousPseudoLength.sq : ∀ {G : Type u} [Group G] {l : G → ℝ},
[2026-06-04T07:22:03] [leanaide.elaboration.info]   IsHomogeneousPseudoLength l → ∀ (g : G), l (g ^ (2 : ℤ)) = 2 * l g := by sorry'
[2026-06-04T07:22:03] [leanaide.papercodes.info] Obtained type: {G : Type u} → [Group G] → (G → ℝ) → Prop
[2026-06-04T07:22:03] [leanaide.papercodes.info] Obtained type in local context: {G : Type u} → [Group G] → (G → ℝ) → Prop
[2026-06-04T07:22:03] [leanaide.codegen.info] Trying automation tactics
[2026-06-04T07:22:03] [leanaide.codegen.info] previous definitions/theorems names: #[]
```

### Prompt sees `IsPseudoLengthFunction`, but candidate checking does not

The first excerpt shows that the generated declaration `IsPseudoLengthFunction` was included in the prompt context. The next excerpt shows theorem-candidate checking using an `example` that does not include that context; Lean then treats both `IsPseudoLengthFunction` and `is_homogeneous_pseudo_length_sq` as unknown identifiers.

```text
[2026-06-04T07:19:26] [leanaide.translate.info] Using command prelude in prompt:
[2026-06-04T07:19:26] [leanaide.translate.info] import Mathlib
[2026-06-04T07:19:26] [leanaide.translate.info] 
[2026-06-04T07:19:26] [leanaide.translate.info] #check "Obtained definition"
[2026-06-04T07:19:26] [leanaide.translate.info] def IsPseudoLengthFunction {G : Type u} [Group G] (l : G → ℝ) : Prop :=
[2026-06-04T07:19:26] [leanaide.translate.info]   (∀ g : G, 0 ≤ l g) ∧ l 1 = 0 ∧ (∀ g : G, l g⁻¹ = l g) ∧ ∀ g h : G, l (g * h) ≤ l g + l h
```

```text
[2026-06-04T07:23:34] [leanaide.elaboration.info] Trying to elaborate '```lean
[2026-06-04T07:23:34] [leanaide.elaboration.info] theorem is_homogeneous_pseudo_length_conj_invariant : ∀ {G : Type u} [Group G] (l : G → ℝ),
[2026-06-04T07:23:34] [leanaide.elaboration.info]   IsPseudoLengthFunction l → is_homogeneous_pseudo_length_sq l → ∀ x y : G, l (y * x * y⁻¹) = l x := by sorry
[2026-06-04T07:23:34] [leanaide.elaboration.info] ```'
[2026-06-04T07:23:34] [leanaide.elaboration.info] Checking groups: 15
[2026-06-04T07:23:34] [leanaide.frontend.info] Running frontend (no cache) on input:
[2026-06-04T07:23:34] [leanaide.frontend.info] example : ∀ {G : Type u} [Group G] (l : G → ℝ),
[2026-06-04T07:23:34] [leanaide.frontend.info]   IsPseudoLengthFunction l → is_homogeneous_pseudo_length_sq l → ∀ x y : G, l (y * x * y⁻¹) = l x := by sorry
[2026-06-04T07:23:34] [leanaide.frontend.info] Running frontend on input:
[2026-06-04T07:23:34] [leanaide.frontend.info] example : ∀ {G : Type u} [Group G] (l : G → ℝ),
[2026-06-04T07:23:34] [leanaide.frontend.info]   IsPseudoLengthFunction l → is_homogeneous_pseudo_length_sq l → ∀ x y : G, l (y * x * y⁻¹) = l x := by sorry
[2026-06-04T07:23:34] [leanaide.frontend.info] Frontend finished with 2 messages
[2026-06-04T07:23:34] [leanaide.frontend.info] Frontend wrote to /Users/gadgil/code/LeanAide/.leanaide_cache/frontend/3052415515688621582_v4.28.0.json with 2 messages
[2026-06-04T07:23:34] [leanaide.elaboration.info] {"parsed":{"cmdErrors":["Function expected at\n  IsPseudoLengthFunction\nbut this term has type\n  ?m.1\n\nNote: Expected a function because this term is being applied to the argument\n  l\n\nHint: The identifier `IsPseudoLengthFunction` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.","Function expected at\n  is_homogeneous_pseudo_length_sq\nbut this term has type\n  ?m.2\n\nNote: Expected a function because this term is being applied to the argument\n  l\n\nHint: The identifier `is_homogeneous_pseudo_length_sq` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement."],"context?":"For every x,y in G, l(yxy^{-1}) = l(x).","elabError":"","text":"∀ {G : Type u} [Group G] (l : G → ℝ),\n  IsPseudoLengthFunction l → is_homogeneous_pseudo_length_sq l → ∀ x y : G, l (y * x * y⁻¹) = l x"}}
```

### Materialized claim fallback for "l is homogeneous"

This excerpt shows an ambient assumption being materialized as an `assert_statement`, then failing translation. It also shows the strict translator rejecting the fallback because the inferred type contains `sorryAx`.

```text
[2026-06-04T07:37:58] [leanaide.elaboration.info] Trying to elaborate 'theorem theorem_positive_integer_homogeneous :
[2026-06-04T07:37:58] [leanaide.elaboration.info]     ∀ {G : Type u} [inst_14157295161945824867 : Group G] (l : G → ℝ) (x : G) (y : G) (n : ℤ),
[2026-06-04T07:37:58] [leanaide.elaboration.info]       0 < n → is_homogeneous_pseudo_length_sq l := by
[2026-06-04T07:37:58] [leanaide.elaboration.info]   sorry'
[2026-06-04T07:37:58] [leanaide.frontend.info] Running frontend (no cache) on input:
[2026-06-04T07:37:58] [leanaide.frontend.info] example : ∀ {G : Type u} [inst_14157295161945824867 : Group G] (l : G → ℝ) (x : G) (y : G) (n : ℤ),
[2026-06-04T07:37:58] [leanaide.frontend.info]   0 < n → is_homogeneous_pseudo_length_sq l := by sorry
[2026-06-04T07:37:58] [leanaide.frontend.info] Running frontend on input:
[2026-06-04T07:37:58] [leanaide.frontend.info] example : ∀ {G : Type u} [inst_14157295161945824867 : Group G] (l : G → ℝ) (x : G) (y : G) (n : ℤ),
[2026-06-04T07:37:58] [leanaide.frontend.info]   0 < n → is_homogeneous_pseudo_length_sq l := by sorry
[2026-06-04T07:37:58] [leanaide.frontend.info] Frontend finished with 1 messages
[2026-06-04T07:37:58] [leanaide.frontend.info] Frontend wrote to /Users/gadgil/code/LeanAide/.leanaide_cache/frontend/17928280048009907639_v4.28.0.json with 1 messages
[2026-06-04T07:37:58] [leanaide.elaboration.info] {"parsed":{"cmdErrors":["Function expected at\n  is_homogeneous_pseudo_length_sq\nbut this term has type\n  ?m.1\n\nNote: Expected a function because this term is being applied to the argument\n  l\n\nHint: The identifier `is_homogeneous_pseudo_length_sq` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement."],"context?":"Fix G : Type u\nFix inst_14157295161945824867 : Group G\nFix l : G → ℝ\nFix x : G\nFix y : G\nAssume that: n is a positive integer.\nThe map \\(l\\) is homogeneous.","elabError":"","text":"∀ {G : Type u} [inst_14157295161945824867 : Group G] (l : G → ℝ) (x : G) (y : G) (n : ℤ),\n  0 < n → is_homogeneous_pseudo_length_sq l"}}
[2026-06-04T07:37:58] [leanaide.frontend.info] Running frontend (no cache) on input:
[2026-06-04T07:37:58] [leanaide.frontend.info] example : ∀ {G : Type u} [inst_14157295161945824867 : Group G] (l : G → ℝ) (x : G) (y : G) (n : ℤ), sorry := by sorry
[2026-06-04T07:37:58] [leanaide.frontend.info] Running frontend on input:
[2026-06-04T07:37:58] [leanaide.frontend.info] example : ∀ {G : Type u} [inst_14157295161945824867 : Group G] (l : G → ℝ) (x : G) (y : G) (n : ℤ), sorry := by sorry
[2026-06-04T07:37:58] [leanaide.frontend.info] Frontend finished with 1 messages
[2026-06-04T07:37:58] [leanaide.frontend.info] Frontend wrote to /Users/gadgil/code/LeanAide/.leanaide_cache/frontend/2986586625238187685_v4.28.0.json with 1 messages
[2026-06-04T07:37:58] [leanaide.frontend.info] Running frontend on input:
[2026-06-04T07:37:58] [leanaide.frontend.info] set_option autoImplicit false in
[2026-06-04T07:37:58] [leanaide.frontend.info] noncomputable def my_shiny_new_theorem : ∀ {G : Type u} [inst_14157295161945824867 : Group G] (l : G → ℝ) (x : G) (y : G) (n : ℤ), sorry := by sorry
[2026-06-04T07:37:58] [leanaide.frontend.info] Frontend finished with 1 messages
[2026-06-04T07:37:58] [leanaide.elaboration.info] Succeeded on sub-line for 'theorem theorem_positive_integer_homogeneous :
[2026-06-04T07:37:58] [leanaide.elaboration.info]     ∀ {G : Type u} [inst_14157295161945824867 : Group G] (l : G → ℝ) (x : G) (y : G) (n : ℤ),
[2026-06-04T07:37:58] [leanaide.elaboration.info]       0 < n → is_homogeneous_pseudo_length_sq l := by
[2026-06-04T07:37:58] [leanaide.elaboration.info]   sorry'
[2026-06-04T07:37:58] [leanaide.codegen.info] Error in getCode `tacticSeq for source {"type": "assert_statement",
[2026-06-04T07:37:58] [leanaide.codegen.info]  "proof_method": "Materialized from deduced_from_claim.",
[2026-06-04T07:37:58] [leanaide.codegen.info]  "claim": "l is homogeneous."}
[2026-06-04T07:37:58] [leanaide.codegen.info] Error: codegen: no valid function found for key assert_statement
[2026-06-04T07:37:58] [leanaide.codegen.info] Tried functions: #[LeanAide.assertionCode]
[2026-06-04T07:37:58] [leanaide.codegen.info] Errors in functions:
[2026-06-04T07:37:58] [leanaide.codegen.info] 
[2026-06-04T07:37:58] [leanaide.codegen.info] LeanAide.assertionCode: codegen: failed to translate 'l is homogeneous.' to a proposition even with 'full statement', error: Failed to infer type forall {G : Type.{u}} [inst_14157295161945824867 : Group.{u} G], (G -> Real) -> G -> G -> Nat -> (sorryAx.{succ u_11} (Lean.Name -> Sort.{u_11}) Bool.false (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.num (Lean.Name.num (Lean.Name.num (Lean.Name.num (Lean.Name.num Lean.Name.anonymous (OfNat.ofNat.{0} Nat 9 (instOfNatNat 9))) (OfNat.ofNat.{0} Nat 125 (instOfNatNat 125))) (OfNat.ofNat.{0} Nat 9 (instOfNatNat 9))) (OfNat.ofNat.{0} Nat 130 (instOfNatNat 130))) (OfNat.ofNat.{0} Nat 125 (instOfNatNat 125))) (OfNat.ofNat.{0} Nat 130 (instOfNatNat 130))) "_sorry") "_@") (OfNat.ofNat.{0} Nat 3649635978 (instOfNatNat 3649635978))) "_hygCtx") "_hyg") (OfNat.ofNat.{0} Nat 18 (instOfNatNat 18)))) has sorry or mvar when translating assertion 'l is homogeneous.', full statement Fix G : Type u
```

### Bare theorem names are not instantiated proof terms

Here `Units.conj_pow` is available as a name, but using the bare name leaves Lean without enough type information.

```text
[2026-06-04T07:44:11] [leanaide.papercodes.info] codegen: failed to create have tactic for 'lean_term' Units.conj_pow for theorem Power of a conjugate with error:
[2026-06-04T07:44:11] [leanaide.papercodes.info] typeclass instance problem is stuck
[2026-06-04T07:44:11] [leanaide.papercodes.info]   Monoid ?m.67
[2026-06-04T07:44:11] [leanaide.papercodes.info] 
[2026-06-04T07:44:11] [leanaide.papercodes.info] Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Monoid` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.
[2026-06-04T07:44:11] [leanaide.papercodes.info] 
[2026-06-04T07:44:11] [leanaide.papercodes.info] Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
[2026-06-04T07:44:12] [leanaide.papercodes.info] Translating to proposition: (y*x*y^{-1})^n = y*x^n*y^{-1}, full statement: Fix G : Type u
[2026-06-04T07:44:12] [leanaide.papercodes.info] Fix inst_14157295161945824867 : Group G
[2026-06-04T07:44:12] [leanaide.papercodes.info] Fix l : G → ℝ
[2026-06-04T07:44:12] [leanaide.papercodes.info] Fix x : G
[2026-06-04T07:44:12] [leanaide.papercodes.info] Fix y : G
[2026-06-04T07:44:12] [leanaide.papercodes.info] Assume that: n is a positive integer.
[2026-06-04T07:44:12] [leanaide.papercodes.info] (y*x*y^{-1})^n = y*x^n*y^{-1}
```

### Source-command failure with mismatched theorem dependencies

This excerpt shows `lemma_11` failing at source processing and also shows unrelated theorem names surviving in `deduced_from_theorem`.

```text
[2026-06-04T14:05:39] [leanaide.codegen.info] Error in processing source for command {"type": "theorem",
[2026-06-04T14:05:39] [leanaide.codegen.info]  "status": "resolved",
[2026-06-04T14:05:39] [leanaide.codegen.info]  "source":
[2026-06-04T14:05:39] [leanaide.codegen.info]  {"text":
[2026-06-04T14:05:39] [leanaide.codegen.info]   "Let A be an abelian group. Let p:A -> R be a homogeneous pseudo-length function.",
[2026-06-04T14:05:39] [leanaide.codegen.info]   "label": "Lemma 11",
[2026-06-04T14:05:39] [leanaide.codegen.info]   "id": "homogeneous.root.lemma-11"},
[2026-06-04T14:05:39] [leanaide.codegen.info]  "proof":
[2026-06-04T14:05:39] [leanaide.codegen.info]  {"type": "proof",
[2026-06-04T14:05:39] [leanaide.codegen.info]   "text":
[2026-06-04T14:05:39] [leanaide.codegen.info]   "By Lemma 10, p vanishes on T(A). The same representative-independence argument used in Lemma 9 shows that p descends to a well-defined function on A/T(A). The quotient map is a homomorphism, so the pseudo-length axioms and homogeneity descend to the quotient.",
[2026-06-04T14:05:39] [leanaide.codegen.info]   "status": "resolved",
[2026-06-04T14:05:39] [leanaide.codegen.info]   "proof_steps":
[2026-06-04T14:05:39] [leanaide.codegen.info]   [{"type": "assert_statement",
[2026-06-04T14:05:39] [leanaide.codegen.info]     "proof_method": "By Lemma 10.",
[2026-06-04T14:05:39] [leanaide.codegen.info]     "deduced_from_theorem":
[2026-06-04T14:05:39] [leanaide.codegen.info]     [{"name": "Lemma 10",
[2026-06-04T14:05:39] [leanaide.codegen.info]       "lean_name": "Polynomial.aeval_eq_zero_of_mem_rootSet",
[2026-06-04T14:05:39] [leanaide.codegen.info]       "description": "Applied to every element of the torsion subgroup T(A).",
[2026-06-04T14:05:39] [leanaide.codegen.info]       "claim": "If a ∈ T(A), then p(a)=0."}],
[2026-06-04T14:05:39] [leanaide.codegen.info]     "claim": "p vanishes on T(A).",
[2026-06-04T14:05:39] [leanaide.codegen.info]     "arguments": []},
[2026-06-04T14:05:39] [leanaide.codegen.info]    {"type": "assert_statement",
[2026-06-04T14:05:39] [leanaide.codegen.info]     "proof_method":
[2026-06-04T14:05:39] [leanaide.codegen.info]     "Use the same representative-independence argument used in Lemma 9, together with the fact that p vanishes on T(A).",
[2026-06-04T14:05:39] [leanaide.codegen.info]     "deduced_from_theorem":
[2026-06-04T14:05:39] [leanaide.codegen.info]     [{"lean_name": "Function.Periodic.lift.congr_simp",
[2026-06-04T14:05:39] [leanaide.codegen.info]       "description":
[2026-06-04T14:05:39] [leanaide.codegen.info]       "Used via the same representative-independence argument as in Lemma 9.",
```

### Construction proof failure in `corollary_15`

This excerpt shows the `construction_proof` path failing to translate the existential full claim without introducing `sorryAx`.

```text
[2026-06-04T16:44:41] [leanaide.codegen.info] LeanAide.constructionProofCode: codegen: failed to translate 'There exists a homogeneous length function on G.' to a proposition even with 'full statement', error: Failed to infer type forall (G : Type.{u}) [inst : Group.{u} G], sorryAx.{succ u_11} (Lean.Name -> Sort.{u_11}) Bool.false (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.num (Lean.Name.num (Lean.Name.num (Lean.Name.num (Lean.Name.num Lean.Name.anonymous (OfNat.ofNat.{0} Nat 9 (instOfNatNat 9))) (OfNat.ofNat.{0} Nat 74 (instOfNatNat 74))) (OfNat.ofNat.{0} Nat 9 (instOfNatNat 9))) (OfNat.ofNat.{0} Nat 79 (instOfNatNat 79))) (OfNat.ofNat.{0} Nat 74 (instOfNatNat 74))) (OfNat.ofNat.{0} Nat 79 (instOfNatNat 79))) "_sorry") "_@") (OfNat.ofNat.{0} Nat 3649635978 (instOfNatNat 3649635978))) "_hygCtx") "_hyg") (OfNat.ofNat.{0} Nat 8 (instOfNatNat 8))) has sorry or mvar when translating assertion 'There exists a homogeneous length function on G.', full statement Fix G : Type u
[2026-06-04T16:44:41] [leanaide.codegen.info] Fix inst : Group G
[2026-06-04T16:44:41] [leanaide.codegen.info] There exists a homogeneous length function on G.; full claim: The group \(G\) admits a homogeneous length function., error: Failed to infer type forall (G : Type.{u}) [inst : Group.{u} G], sorryAx.{succ u_11} (Lean.Name -> Sort.{u_11}) Bool.false (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.num (Lean.Name.num (Lean.Name.num (Lean.Name.num (Lean.Name.num Lean.Name.anonymous (OfNat.ofNat.{0} Nat 9 (instOfNatNat 9))) (OfNat.ofNat.{0} Nat 74 (instOfNatNat 74))) (OfNat.ofNat.{0} Nat 9 (instOfNatNat 9))) (OfNat.ofNat.{0} Nat 79 (instOfNatNat 79))) (OfNat.ofNat.{0} Nat 74 (instOfNatNat 74))) (OfNat.ofNat.{0} Nat 79 (instOfNatNat 79))) "_sorry") "_@") (OfNat.ofNat.{0} Nat 3649635978 (instOfNatNat 3649635978))) "_hygCtx") "_hyg") (OfNat.ofNat.{0} Nat 8 (instOfNatNat 8))) has sorry or mvar when translating assertion 'The group \(G\) admits a homogeneous length function.', full statement Fix G : Type u
[2026-06-04T16:44:41] [leanaide.codegen.info] Fix inst : Group G
[2026-06-04T16:44:41] [leanaide.codegen.info] The group \(G\) admits a homogeneous length function.
[2026-06-04T16:44:41] [leanaide.codegen.info] source:
```

## Run statistics

The log has 276,504 lines and records 535 `"Trying to elaborate"` attempts and 364 OpenAI API payloads.

The generated Lean has 1,674 lines. Its footer reports:

- 29 elaboration log entries
- 15 declarations
- 10 `"declaration uses sorry"` log entries
- 4 top-level commands skipped because of source-processing errors
- 31 sorry goals
- `Sorries after purge: none`

Direct counts in `CodeGen/homogeneous.lean`:

- 108 occurrences of the token `sorry`
- 87 occurrences of `repeat (sorry)`
- 31 `skip` tactics
- 7 metavariable placeholders of the form `?m...`

The JSON has 4,645 lines and a top-level document body with:

- 4 definitions
- 15 theorems
- 8 sections
- 4 check entries
- 1 paragraph

The JSON no longer contains a `deduced_from_claim` key. It does contain 134 proof-method strings equal to `"Materialized from deduced_from_claim."`, meaning the dependencies were converted into explicit `assert_statement`s. This avoids the forbidden key, but the resulting haves are often ungrounded or too informal.

The JSON has 125 `deduced_from_theorem` references:

- 118 include a `lean_name`
- 0 include a `lean_term`
- 7 include neither `lean_name` nor `lean_term`

This is a major residual Python-side issue: the earlier requirement was that when a theorem is used after instantiation, the object should include a `lean_term`. In this run no theorem dependency has one.

## Definition translation failures

### `IsLength` became `True`

The source definition says:

```text
Let G be a group with identity element e. A pseudo-length function l : G -> R is a length function if, for every g in G, g != e implies 0 < l(g).
```

The LLM proposed the essentially correct command:

```lean
def IsLength {G : Type u} [Group G] (l : G -> R) : Prop :=
  IsPseudoLengthFunction l /\ forall g : G, g != 1 -> 0 < l g
```

But the generated Lean contains:

```lean
noncomputable def isLength_of_pos_of_ne_one :
    {G : Type u} -> [Group G] -> (G -> R) -> Prop :=
  by
  intro G
  intro inst
  intro f
  exact True
```

The log explains why. During definition translation, the elaborator accepted only the type of the command, namely `{G : Type u} -> [Group G] -> (G -> R) -> Prop`, and then automation filled that type with `True`. The body of the LLM-produced definition was not preserved.

This is a Lean codegen defect in the definition path. `LeanAideCore/LeanAideCore/PaperCodes.lean` first tries `translator.translateDefCmdM?`, but on failure it falls back to translating an existential proposition `"There exists <name> such that: ..."`. That fallback can produce only a type, not the intended definition body. The definition handler then accepts an arbitrary inhabitant of the function-to-Prop type.

Universal fix:

- A definition handler must preserve the translated definition command, including its body.
- It must reject fallback results whose generated definition is extensionally just `True`, a bare `Prop`, a theorem about existence, or a type-valued shell.
- When translating a definition, ask the LLM for exactly one `def <requested_name> ... := ...`; do not allow it to append theorems or helper declarations.
- Add a semantic validation step: the generated body must mention the important predicates and variables from the source, e.g. for this case `IsPseudoLengthFunction`, `g != 1`, and `0 < l g`.

### `IsHomogeneousPseudoLength` became `True`

The source says homogeneity means:

```text
forall g in G and every integer n, l(g^n) = |n| l(g)
```

The prompt included prior code context, and the LLM proposed a useful definition:

```lean
def IsHomogeneousPseudoLength {G : Type u} [Group G] (l : G -> R) : Prop :=
  IsPseudoLengthFunction l /\ forall (g : G) (n : Z), l (g ^ n) = |(n : R)| * l g
```

The generated file instead contains:

```lean
noncomputable def is_homogeneous_pseudo_length_sq :
    {G : Type u} -> [Group G] -> (G -> R) -> Prop :=
  by
  intro G
  intro inst
  intro f
  exact True
```

This is the same failure pattern as `IsLength`. It is especially damaging because nearly every later theorem depends on homogeneity.

Universal fix:

- Do not translate a definition as "there exists a definition".
- If the first candidate is a valid `def`, accept the actual command, not just its type.
- Keep requested naming stable: the JSON name is `IsHomogeneousPseudoLength`, but the generated Lean name is `is_homogeneous_pseudo_length_sq`. Name drift makes later translation fragile.

## Theorem statement drift

Several generated theorem statements are not the statements of the source mathematics. This is not merely proof failure; it is incorrect translation.

### `lemma_1` omits assumptions on `l`

Generated:

```lean
theorem lemma_1 :
  forall {G : Type u} [Group G] (l : G -> R) (x y : G),
    l (y * x * y^-1) = l x := ...
```

This is false for an arbitrary function `l : G -> R`. The statement needs assumptions that `l` is at least a homogeneous pseudo-length function. The proof later tries to assert `"l is homogeneous."`, but that should be part of the theorem context, not a proof step materialized from a local claim.

Python-side cause: the document parser represents "Let G be a group. Let l be a homogeneous pseudo-length function." as informal source context, but the theorem object claim is only `"For every x,y in G, ..."`. The context is not promoted to formal theorem parameters/hypotheses.

Lean-side cause: once the incorrect theorem statement is accepted, the proof generator tries to recover missing hypotheses by generating haves like:

```lean
have assert_... : ... := by repeat (sorry)
```

Universal fix:

- The JSON theorem object should have explicit formal context fields: parameters, typeclass assumptions, named hypotheses, and ambient assumptions inherited from the current section.
- Translation prompts for theorem claims should include the full source prelude and require every assumption used in the proof to appear either in the statement or as an already available local hypothesis.
- Proof generation should not manufacture a hypothesis such as "l is homogeneous" unless it is introduced by the theorem statement or by a previously proved local lemma.

### `lemma_2` omits the recursive definition of `C`

Generated:

```lean
theorem lemma_2 :
  forall {G : Type u} [Group G] (l : G -> R) (C : Nat -> G) (s t y z : G) (n : Nat),
    l (C n) <= l s^-1 + l t + n * (l y + l z)
```

This cannot be true for an arbitrary sequence `C`. The proof later invents:

```lean
have assert_... : forall (n : Nat), n = 0 := by repeat (sorry)
have assert_... : forall (w : G) (n : Nat), C (n + 1) = w * y * C n * z * w^-1 := by repeat (sorry)
```

These are not proof obligations; they are missing hypotheses or definitions. The first one is simply false. This is a Python proof-planning failure: a side condition for the base case was generalized into `forall n, n = 0`.

Universal fix:

- Side conditions must be tied to the current local variables and branch context. In an induction base case, "n = 0" should not become `forall n, n = 0`.
- Definitions introduced in prose, such as the recurrence for `C`, must be represented as named assumptions or a `let`/`where` construction before codegen.
- Add a proof-sanity pass that rejects universalizations of branch-local equalities and detects obviously false claims such as `forall n : Nat, n = 0`.

## Source-level command failures

The generated Lean has four skipped commands corresponding to four theorem objects.

### `lemma_11`: quotient factorization of `p`

Source claim:

```text
The function p factors through the quotient of A by its torsion subgroup.
The induced function on that quotient is again a homogeneous pseudo-length function.
```

The log shows source-processing failure for `lemma_11`. The attempted proposition contained an existential `pbar`, but the induced homogeneous-pseudo-length property was elaborated as a `sorryAx` inside the type. `translateToPropStrict` rejected it as containing sorry/metavariables.

Python-side problem:

- `deduced_from_theorem` gave irrelevant or mismatched theorem names, e.g. `Polynomial.aeval_eq_zero_of_mem_rootSet` for "Lemma 10" and `Function.Periodic.lift.congr_simp` for quotient descent.
- The claim "the induced function is homogeneous pseudo-length" requires a structured statement about quotient maps and compatibility, not a prose assertion.

Lean-side problem:

- The translator has no stable formal definition of homogeneous pseudo-length because earlier definitions collapsed to `True`.
- The proposition translator can produce partial types containing `sorryAx`; those must be rejected earlier and diagnosed as an incomplete translation, not carried into later codegen.

Universal fix:

- For quotient descent, Python should emit an explicit construction record: quotient type, quotient map, lifted function, proof of well-definedness, and inherited axioms.
- Lean theorem lookup must verify that a `lean_name` has a type matching the requested theorem. A theorem about polynomial roots should not survive as evidence for a torsion subgroup lemma.

### `lemma_12`: rationalization and seminorm extension

Source claim:

```text
There exists a seminorm normQ on VQ such that normQ(a tensor 1)=p(a) for every a in A.
```

The JSON proof uses informal fraction language:

```text
Every element of VQ can be written as a/n with a in A and n positive.
If a/n=b/m ...
```

This is mathematically meaningful, but it is not a Lean-ready representation of tensor products. The generated dependencies include names such as `Algebra.TensorProduct.intCast_def` and `Rat.divInt_eq_divInt`, which do not encode the needed universal property or quotient relation for `A tensor_Z Q`.

Universal fix:

- Python should not emit "a/n" notation for tensor-product elements unless a concrete Lean representation has been chosen.
- The proof planner should choose one formal construction style and keep it throughout: either tensor product universal properties, localization, or a quotient construction of rational multiples.
- The generated JSON should include concrete maps and types: `A -> A tensor_Z Q`, scalar ring, target module, and the defining equation for the extension.

### `theorem_14`: Banach-space representation

Theorem 14 fails because it depends on the missing `lemma_11` and `lemma_12`, and because its `let_statement`s are too informal:

```text
Let barL be the homogeneous pseudo-length function from GAb to R induced by l...
Let A be the quotient of GAb by the torsion subgroup...
Let VQ be A tensor over Z with Q...
```

These are constructions with dependent data, not simple local variables. The Lean codegen path for `let_statement` in `LeanAide/PaperCodes.lean` asks the translator to "Define ONLY the term <varName> with value <value>". For values like "GAb to R" or "real Banach space obtained from Lemma 13", that is not enough information to construct a typed Lean term.

Universal fix:

- Treat construction steps as structured existential eliminations from prior theorems, not as free-form `let_statement`s.
- If a prior theorem gives `exists B, exists phi, P B phi`, the JSON should name the theorem result and specify destructuring fields, not ask the translator to invent `B` and `phi` from prose.
- Python should emit `lean_term` for each destructuring use, e.g. an exact local theorem application, then Lean codegen can produce `obtain`/`rcases`.

### `corollary_15`: bi-implication with construction proof

The corollary fails in the `bi-implication_cases_proof` path. The `only_if_proof` uses a `construction_proof` whose `full_claim` is:

```text
There exists a homogeneous length function on G.
```

The proposition translator tries to formalize this as:

```lean
exists l : G -> R, isLength_of_pos_of_ne_one l /\ is_homogeneous_pseudo_length_sq l
```

but at the elaboration stage `isLength_of_pos_of_ne_one` and `is_homogeneous_pseudo_length_sq` are treated as unknown identifiers in the checking context. The log records repeated "Function expected at ..." errors for both names.

Universal fix:

- The elaboration checker must run candidate translations in the actual generated module context, with prior generated declarations imported or inserted.
- The prompt and the checker must agree about available names. It is not enough to show previous code in the prompt if the frontend check uses only `example : ...` without that code.
- Generated theorem statements should use the requested definition names consistently; avoid switching between `IsLength`, `isLength_of_pos_of_ne_one`, and other variants.

## Elaboration failure categories

From parsed elaboration records in the log:

- 2,092 parsed error records
- 1,729 unknown identifier / "Function expected at" records
- 428 type mismatch records
- 329 typeclass synthesis records
- 103 application type mismatch records
- 24 records involving sorry/metavariables in an inferred type

The largest class is not hard mathematics; it is context mismatch. Example:

```text
Function expected at
  is_homogeneous_pseudo_length_sq
but this term has type ?m.1
Hint: The identifier `is_homogeneous_pseudo_length_sq` is unknown...
```

This occurs even though the generated Lean file contains a declaration with that name. The candidate was checked in a frontend input of the form:

```lean
example : forall {G : Type u} [Group G] (l : G -> R),
  is_homogeneous_pseudo_length_sq l -> ... := by sorry
```

without the previous generated declarations in scope.

Universal Lean-side fix:

- Every call to `bestElab?`, `checkElabFrontM`, or theorem-candidate checking should include the current command prelude, generated declarations, and section-local context.
- If that is too expensive, create a temporary module prefix containing the generated code with theorem proofs replaced by `sorry`, and elaborate candidates after that prefix.
- Set `autoImplicit false` for checks earlier, so unknown identifiers are rejected directly rather than becoming metavariables that later fail as "Function expected".

## Bad fallback: "Succeeded on sub-line"

The log contains 182 `"Succeeded on sub-line"` messages. These are risky. A representative failure:

```text
Trying to elaborate theorem theorem_positive_integer_homogeneous :
  forall ... 0 < n -> is_homogeneous_pseudo_length_sq l := by sorry
```

After `is_homogeneous_pseudo_length_sq` fails as unknown, the frontend checks:

```lean
example : forall ... , sorry := by sorry
```

and logs "Succeeded on sub-line". This is not a successful translation. It is a partial fallback that replaced the failed target by `sorry`.

Universal fix:

- Strict translation paths must reject any fallback whose resulting expression contains `sorryAx`, metavariables, or a type that is only the prefix of the intended proposition.
- "Succeeded on sub-line" should be diagnostic only. It should not feed codegen unless the caller explicitly requested partial translation.
- The reportable error should retain the original failed candidate, the truncated accepted sub-line, and the reason truncation was used.

## `deduced_from_theorem` handling

The Lean handler in `LeanAideCore/LeanAideCore/PaperCodes.lean` treats `lean_name` as a fallback `lean_term`:

```lean
match data.getObjValAs? String "lean_term" with
| ok t => some t
| error _ =>
  match data.getObjValAs? String "lean_name" with
  | ok n => some n
```

It then parses the string as a term and attempts:

```lean
have name : stx := by apply stx
```

This works only if the theorem constant itself has exactly the needed target after all implicit arguments can be inferred. In this run it usually does not. The log has 48 failures of the form:

```text
codegen: failed to create have tactic for 'lean_term' Units.conj_pow ...
typeclass instance problem is stuck
  Monoid ?m...
```

Other failed names include `ge_antisymm`, `CoxeterSystem.length_mul_le`, `ConjAct.ofConjAct_toConjAct`, `dist_triangle`, `FreeGroup.norm_mul_le`, `UniformSpace.Completion.extension_unique`, `Subgroup.comap_injective_isMulCommutative`, and `IsAddTorsionFree.zsmul_eq_zero_iff_right`.

There are two distinct defects:

1. Many `lean_name`s are not theorems matching the desired claim. Examples: `Polynomial.aeval_eq_zero_of_mem_rootSet` for a torsion subgroup vanishing lemma, `NormedAddGroupHom.completion_coe` for Theorem 14, and `Rat.norm_cast_real` for Lemma 13.

2. Even when the name is relevant, it is not instantiated. A bare theorem name is rarely a usable proof of the current assertion.

Universal fix:

- Python must emit `lean_term` whenever the theorem is used at specific variables, hypotheses, or arguments. This did not happen in the current JSON: zero `deduced_from_theorem` entries have `lean_term`.
- Lean codegen should not use `lean_name` as a proof term. It should first infer the theorem type, try to synthesize an application to the target, and only emit a have if the resulting term type is definitionally equal or unifies with the target.
- LeanSearch/local search should return candidates, but a separate verifier must check exact type compatibility with the requested claim before the name enters JSON.
- If no exact term is found, Python should emit a named proof obligation rather than a fake theorem dependency.

## Materialized `deduced_from_claim` haves

The key `deduced_from_claim` has been removed, but the materialization pass creates proof steps like:

```json
{
  "type": "assert_statement",
  "claim": "l is homogeneous.",
  "proof_method": "Materialized from deduced_from_claim."
}
```

This is better than emitting the unsupported key, but it still produces Lean-facing obligations that often cannot be translated. The log has 49 `"failed to translate"` records, many caused by these materialized claims.

Representative failure:

```text
LeanAide.assertionCode: failed to translate 'l is homogeneous.'
full statement:
Fix G : Type u
Fix inst : Group G
Fix l : G -> R
...
Assume that: n is a positive integer.
l is homogeneous.
```

The correct action was not to prove a new local assertion. It was to have `l`'s homogeneity as a theorem hypothesis or a field of a structure passed into the theorem statement.

Universal fix:

- Materialization should be a last-resort transformation only after checking whether the claim is already a hypothesis, a field projection from an assumption, or an instantiation of a prior theorem.
- If a claim is an ambient hypothesis, omit it.
- If it is a specialization, emit a `specialize`/local-lemma object with `name` and concrete `lean_term`.
- If it genuinely needs proof, create a named local theorem obligation with full source context and expected Lean statement, not a raw `assert_statement` from prose.
- Add a final JSON audit that counts `"Materialized from deduced_from_claim."` and fails the pipeline unless each materialized assertion has a formal target or a verified source theorem.

## Proof completion failures

The bottom of `CodeGen/homogeneous.lean` lists 31 sorry goals. They fall into these categories.

### Missing theorem hypotheses

Examples:

- `lemma_1`: homogeneity, symmetry, triangle inequality, and nonnegativity are all used but not in the theorem statement.
- `lemma_2`: the recurrence defining `C` is used but not in the theorem statement.
- `lemma_3`: conjugacy witnesses and positivity assumptions are repeatedly invented as haves.

Universal fix:

- The proof planner should never use a property in a proof unless it is present in the theorem statement, a named previous theorem, a field of an existing structure, or a locally introduced construction.

### False or overgeneralized local claims

Examples:

```lean
have assert_... : forall (n : Nat), n = 0 := by repeat (sorry)
```

and:

```lean
have assert_... : forall (w : G) (n : Nat), C (n + 1) = w * y * C n * z * w^-1 := by repeat (sorry)
```

These arise when side conditions or definitions are extracted from prose without scope.

Universal fix:

- Counterexample construction should be applied to every generated local assertion, not just top-level lemmas.
- Quantifier drift detection should flag claims where a local side condition is generalized over the variable it constrains.

### Domain-specific construction gaps

The later functional-analysis/algebra construction around completions has goals with metavariables such as:

```lean
have assert_exists_... :
  have homogeneous_root_lemma_13_proof_root_zero_subspace : forall (N : Submodule Q V_Q), True := ...
  ?m.3797
```

This means the construction proof did not know the exact existential target at the point where it attempted to build the witness. Generated code contains nested `?m...` goals, placeholder `True` lemmas, and duplicated construction blocks.

Universal fix:

- Construction proof JSON must have a formal `full_claim` that Lean can elaborate before witness generation begins.
- Existential construction code should reject unknown target metavariables instead of generating `?m...`-typed haves.
- For complex constructions, split "choose object", "define structure", and "verify properties" into separate JSON nodes with exact Lean types.

## Why `addDefn` did not prevent the context failure

The `IsPseudoLengthFunction` failure is initially surprising because `LeanAideCore/LeanAideCore/TranslateM.lean` defines:

```lean
def addDefn (dfn: DefData) : TranslateM Unit := do
  runCommand <| ← dfn.statementStx
  modify fun s => {s with defs := s.defs.push dfn}
```

and `runCommand` calls `runFrontendM ... true`, which should modify the current Lean environment:

```lean
def runCommand (cmd: Syntax.Command) : TranslateM Unit := do
  discard <|  runFrontendM (← ppCommand cmd).pretty true
  modify fun s  => {s with cmdPrelude := s.cmdPrelude.push cmd}
```

The logs and code show that this is not enough, because generated declarations are tracked in several different places that are not kept synchronized.

1. `cmdPrelude` is used as prompt text, not automatically as checker context. `cmdPreludeBriefBlob?` converts stored commands to a string beginning with `import Mathlib`, and `Translator.getMessages` places that string in the LLM prompt. This is why the prompt excerpt contains `def IsPseudoLengthFunction ...`. But `translateDefCmdM?` validates each candidate by calling `checkElabFrontM s` on only the candidate string. It does not prepend or re-elaborate the `cmdPrelude` command sequence as part of the checked input.

2. The frontend cache is context-insensitive. In `LeanAideCore/LeanAideCore/SimpleFrontend.lean`, `runFrontEndForMessages` caches by `input.hash` and Lean toolchain:

```lean
let cacheFile := (← cachePath) / "frontend" / s!"{input.hash}_{← leanToolchain}.json"
```

The key does not include an environment fingerprint or the generated declaration prelude. A frontend check result for `example : ...` can therefore be reused even if the surrounding generated environment has changed. The `IsHomogeneousPseudoLength` excerpt shows this exact hazard: the checker reads a cached result for the bare type `{G : Type u} -> [Group G] -> (l : G -> R) -> Prop`.

3. `addCommand` and `addCommands` are prompt-only operations. In `TranslateM.lean`, both only mutate `cmdPrelude`; unlike `addDefn`, they do not call `runFrontendM ... true`. But `LeanAideCore/LeanAideCore/CodegenCore.lean` appends generated command blocks with `Translate.addCommands code`, and `LeanAideCore/LeanAideCore/PaperCodes.lean` adds dummy theorem statements for prompt continuity with `Translate.addCommand dummyCmd`. These commands can appear in later prompts without necessarily being present as elaborated declarations in the environment used by candidate checks.

4. Some state updates happen inside `withoutModifyingState`. `getCodeCommands` is wrapped in `withoutModifyingState`, and theorem proof generation repeatedly uses `withoutModifyingState` around local context construction. This is useful for avoiding prompt pollution from speculative proof attempts, but it makes it especially important to distinguish persistent environment registration from prompt-only state. The current names `addCommand`, `addCommands`, and `addDefn` hide that distinction.

5. The checker and the final generated file are not the same thing. The final `CodeGen/homogeneous.lean` may contain `def IsPseudoLengthFunction`, but an earlier candidate check can still run on `example : ... IsPseudoLengthFunction l ...` without that declaration in the active frontend environment. The unknown-identifier errors are therefore genuine checker-context failures, not evidence that the final file lacks the declaration.

The general fix is to make declaration context a single explicit object. Every translation prompt and every candidate elaboration should be built from the same generated-code prefix. If a candidate is checked with prior code in the prompt, the frontend check should either:

- run in a Lean environment produced by elaborating exactly that prior code with `modifyEnv := true`, or
- check the concatenated command sequence `priorGeneratedCommands ++ candidate` with `autoImplicit false`.

The cache key for frontend messages must include a digest of this context, or caching must be disabled for context-sensitive checks. After `addDefn`, codegen should verify `getEnv.find? name` and log whether the declaration was actually added to the environment. The API should also be renamed or split so that prompt-only operations (`addPromptCommand`) cannot be mistaken for environment registration (`registerCommandInEnv`).

## Prompt improvements

The logs show that the current prompts already include examples and sometimes include a "Code context" section. That is the right direction, but the context is not enforced by elaboration and is not specific enough for proof steps.

Universal prompt changes:

1. Include the generated code so far in every translation prompt, with earlier theorem proofs replaced by `by sorry` for brevity. This reduces translation drift and stabilizes names.

2. Include the source text as a docstring or structured `source` field for every definition, theorem, and generated local obligation. The Python code already emits `source` for top-level definitions/theorems; extend this to generated proof obligations.

3. Tell the LLM to output exactly one declaration or one term, depending on the request. For definition translation, forbid appended theorems. For proposition translation, forbid code fences and declarations unless explicitly requested.

4. Include the local Lean context in machine-readable form:

```text
Available variables:
G : Type u
inst : Group G
l : G -> R
h_l : IsHomogeneousPseudoLength l

Available previous declarations:
IsPseudoLengthFunction : ...
IsHomogeneousPseudoLength : ...
lemma_1 : ...
```

5. Require the output to use only identifiers from Mathlib, the provided generated code, or the listed local context. Unknown identifiers should be treated as invalid.

6. For theorem lookup, ask the LLM for an exact instantiated Lean term, not merely a theorem name:

```text
Target:
  (y * x * y^-1) ^ n = y * x^n * y^-1

Return:
  { "lean_name": "conj_pow", "lean_term": "conj_pow y x n" }
```

Then verify in Lean that the term has the target type before accepting it.

7. For local proof steps, ask first for a Lean proposition only. If the proposition cannot be expressed without inventing new identifiers, return a structured construction/obligation object, not an informal assertion.

## Lean-side recommendations

1. Fix definition codegen so accepted definitions preserve their body. Reject Prop-valued shells generated by existential fallback.

2. Run elaboration of candidates in the same command context that was shown in the prompt. A prompt context without an elaboration context causes the unknown-identifier failures seen for `IsPseudoLengthFunction`, `isLength_of_pos_of_ne_one`, and `is_homogeneous_pseudo_length_sq`.

3. Make `autoImplicit false` the default for candidate checking. Unknown names should fail immediately.

4. Treat "Succeeded on sub-line" as failure for strict translation. Do not use sub-line results containing `sorry`.

5. In `assertionCode`, do not treat `lean_name` as `lean_term`. Use theorem-name lookup only to infer the theorem type and synthesize a checked application to the target.

6. If an assertion proof cannot be generated, emit a named sorry obligation with the exact target and source, rather than inserting arbitrary `repeat (sorry)` haves throughout the proof.

7. Reject generated haves whose type contains metavariables (`?m`) or whose proof target is only `True` unless the source claim is explicitly trivial.

8. Add source JSON paths to all generated Lean diagnostics. The footer currently lists declaration names and goals, but it does not identify the exact JSON pointer that produced each sorry.

## Python-side recommendations

1. Preserve section context as formal theorem hypotheses. Ambient assumptions such as "l is a homogeneous pseudo-length function" must not be left only in prose.

2. Stop emitting unverified `lean_name`s. LeanSearch/local search should produce candidates, but JSON should include a theorem dependency only after exact or near-exact type verification.

3. Emit `lean_term` for every instantiated theorem use. The current run emits none.

4. Add a final audit for materialized claim haves. A raw `"Materialized from deduced_from_claim."` assertion should be accepted only if it has a verified formal statement and proof source.

5. Add counterexample/consistency checks for every generated local assertion, not just top-level lemmas.

6. Represent constructions explicitly. Quotients, tensor products, completions, induced functions, and maps should be JSON objects with names, types, defining maps, and required properties.

7. For complex "there exists" proofs, emit destructuring instructions from prior theorem applications instead of informal `let_statement`s.

8. Keep names stable. If the JSON name is `IsHomogeneousPseudoLength`, the generated Lean should not silently rename it to `is_homogeneous_pseudo_length_sq`.

## Priority fixes

1. Fix definition translation/body preservation. This is the highest priority because all later statements depend on the definitions.

2. Use the generated code-so-far as both prompt context and elaboration context. This addresses the dominant unknown-identifier failure class.

3. Add formal theorem context extraction in Python so top-level hypotheses are not materialized as proof haves.

4. Require and verify `lean_term` for instantiated theorem dependencies.

5. Reject strict translations that contain `sorryAx`, metavariables, or sub-line fallbacks.

6. Replace raw materialized deduced-from-claim assertions with either omitted hypotheses, checked specializations, or named local theorem obligations.
