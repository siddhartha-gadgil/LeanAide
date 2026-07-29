# Prompt Improvements from Recent Codegen Logs

This report extracts prompt-level failure examples from the recent logs, mainly
`.logs/2026-07-28.log` and `.logs/2026-07-27.log`.  The logged LLM payloads are
large JSON strings containing examples, code context, local context, and the
task.  The excerpts below are unescaped from those JSON strings.  Unless a block
is explicitly described as a full prompt, it is a selected slice: usually the
task tail and the specific confusing context, not the whole message.

There are two different prompt classes in the examples:

- translation prompts, which ask the model to translate natural-language or
  semi-formal text into Lean syntax;
- proof/tactic prompts, which ask the model to prove an already fixed Lean goal.

The dominant issue is not simply missing context.  Translation prompts often
contain a useful formal local context, but then mix it with stale or enclosing
prose such as `Current goal`, `## Theorem`, and `Translate the following
statement`.  In nested assertion and branch-local calls this nudges the model
toward generating a new top-level theorem rather than a local proposition or
term.  Proof/tactic prompts have a different failure mode: the prompt form is
usually appropriate, but the target sometimes already contains stale
theorem-shaped binders before the prompt is sent.

## Example 1: local assertion translation prompt regenerates the whole theorem

Source: `.logs/2026-07-28.log:127619`, response at
`.logs/2026-07-28.log:127639--127654`.

Prompt kind: **translation**, not proving.  This prompt was issued while
processing a local `assert_statement` inside the proof of Lemma 4, namely the
claim

```text
f applied to m and k <= (f applied to m - 1 and k + f applied to m + 1 and k - 1) / 2
```

The immediate job should have been to translate that branch-local claim into a
Lean proposition in the current local context, or into the local assertion shape
expected by `assertionCode`.  It was not a request to prove the claim and not a
request to generate the top-level theorem `lemma_4`.

The following is **not the full prompt**.  The full prompt also contains the
standard instruction header, examples, and generated code context.  This first
excerpt is the useful local-context portion of the prompt tail:

```text
Available variables:
(G : Type u_16)
[inst_14157295161945824867 : Group G]
(l : G → ℝ)
(a_8164486838467395441 : IsHomogeneousPseudoLength G ℝ l)
(x : G)
(y : G)
let c : G := x * y * x⁻¹ * y⁻¹
let f : ℤ → ℤ → ℝ := fun m k => l (x ^ m * c ^ k)
(m : ℤ)
(k : ℤ)
let a : G := x ^ m * c ^ k
let w : G := x
let u : G := x ^ (m - 1) * c ^ k
let v : G := y⁻¹ * x ^ m * c ^ (k - 1) * x * y
```

The next excerpt is the problematic task portion of the same prompt tail.  This
is the unnecessary/confusing part: it asks for `## Theorem` translation and
includes the enclosing theorem as `Current goal`, although this is only a local
assertion claim:

```text
Translate the following statement into Lean 4:
## Theorem: Assume that: G is a group.
Assume that: l : G -> R is a homogeneous pseudo-length function.
Assume that: x,y are elements of G.
Assume that: Let G be a group
Assume that: Let l : G -> R be a homogeneous pseudo-length function
Assume that: Fix x,y in G and set c:=[x,y]
Current goal (context only; not an available theorem):
          ∀ (G : Type u_16) [inst : Group G] (l : G → ℝ),
  IsHomogeneousPseudoLength G ℝ l →
    ∀ (x y : G),
      have c := x * y * x⁻¹ * y⁻¹;
      have f := fun m k => l (x ^ m * c ^ k);
      ∀ (m k : ℤ), f m k ≤ (f (m - 1) k + f (m + 1) (k - 1)) / 2
Fix f : ℤ → ℤ → ℝ := fun m k => l (x ^ m * c ^ k)
Fix m : ℤ
Fix k : ℤ
Assume that: m and k are arbitrary integers
Define a to be x^m * c^k.
Define w to be x.
Define u to be x^(m - 1) * c^k.
Define v to be inverse y * x^m * c^(k - 1) * x * y.
f applied to m and k <= (f applied to m - 1 and k + f applied to m + 1 and k - 1) / 2

Give ONLY the Lean code
```

All returned candidates follow the stale top-level cue and regenerate `lemma_4`
instead of translating the local target proposition:

```lean
theorem lemma_4 :
    ∀ (G : Type u_16) [inst : Group G] (l : G → ℝ),
      IsHomogeneousPseudoLength G ℝ l →
        ∀ (x y : G),
          have c : G := x * y * x⁻¹ * y⁻¹
          have f : ℤ → ℤ → ℝ := fun m k => l (x ^ m * c ^ k)
          ∀ (m k : ℤ), f m k ≤ (f (m - 1) k + f (m + 1) (k - 1)) / 2 := by
  sorry
```

Diagnosis:

- The prompt type says `## Theorem`, even though codegen is translating a local
  assertion claim inside an existing proof.
- The phrase `Current goal` shows the enclosing theorem, not just the target
  proposition being translated.
- `Give ONLY the Lean code` is too broad for a nested translation call: a theorem
  command is Lean code, even though this call wanted only local assertion syntax
  or a proposition term.

General fix:

- Split theorem-statement translation, local-assertion translation, term
  translation, and tactic proof generation into different prompt modes.
- For local assertions, use a prompt shaped like:

```text
Task: translate the Target proposition below as a proposition in the current
local context.  Do not generate a theorem, lemma, def, example, or proof.
Return only a Lean proposition term.

Available variables:
...

Target proposition:
  f m k ≤ (f (m - 1) k + f (m + 1) (k - 1)) / 2

Outer theorem, for orientation only:
  ...
```

- If a proof is wanted in a later stage, use a proof/tactic prompt instead:

```text
Task: prove the exact target below in the current local context.
Return only a `by ...` proof.  Do not restate the theorem and do not introduce
new top-level declarations.
```

Implementation sites:

- `LeanAideCore/LeanAideCore/Translator.lean`, where the generic
  `Translate the following statement into Lean 4` wrapper is constructed.
- `LeanAideCore/LeanAideCore/PaperCodes.lean`, especially `assertionCode`,
  `proofCode`, and the places that add `Current goal` to `promptContext`.

## Example 2: induction-branch translation prompt has correct formal context but stale prose

Source: `.logs/2026-07-28.log:24924`, response at
`.logs/2026-07-28.log:24944`.

Prompt kind: **translation**, not proving.  This prompt was issued inside the
successor branch of an induction in Lemma 2 while translating a branch-local
assertion:

```text
C (n + 1) = w * (y * C n * z) * w⁻¹
```

The Meta/local context has the induction hypothesis; this appears in nearby
trace lines, for example `.logs/2026-07-28.log:24910`:

```text
(ih : l (C n) ≤ l s⁻¹ + l t + ↑n * (l y + l z))
```

The following excerpt is **not the full prompt**.  It is the problematic task
tail.  The LLM prompt presents the prose part without `ih` and with the outer
theorem still labelled as `Current goal`:

```text
Translate the following statement into Lean 4:
## Theorem: Assume that: G is a group.
Assume that: l : G -> R is a homogeneous pseudo-length function.
Assume that: w,y,z,s,t are elements of G.
Assume that: Let G be a group
Assume that: Let l : G -> R be a homogeneous pseudo-length function
Assume that: Let w,y,z,s,t in G
Current goal (context only; not an available theorem):
          ∀ (G : Type u_14) [inst : Group G] (l : G → ℝ),
  IsHomogeneousPseudoLength G ℝ l →
    ∀ (w y z s t : G),
      have C := fun n => (w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n;
      ∀ (n : ℕ), l (C n) ≤ l s⁻¹ + l t + ↑n * (l y + l z)
Fix s : G
Fix t : G
Fix C : ℕ → G := fun n => (w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n
Fix n : ℕ
C (n + 1) = w * (y * C n * z) * w⁻¹

Give ONLY the Lean code
```

The model again emits a theorem command.  It also invents a theorem-level `ih`
argument because the prompt did not present the branch as a branch-local
translation target:

```lean
theorem lemma_2 :
    ∀ (G : Type u_14) [inst_14157295161945824867 : Group G] (l : G → ℝ)
      (a_8164486838467395441 : IsHomogeneousPseudoLength G ℝ l)
      (w y z s t : G),
      let C : ℕ → G := fun n => (w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n
      ∀ (n : ℕ)
        (ih : l (C n) ≤ l s⁻¹ + l t + ↑n * (l y + l z)),
        C (n + 1) = w * (y * C n * z) * w⁻¹ := by
  sorry
```

Diagnosis:

- The formal branch context contains `ih`, but the prose `Fix ...` list does
  not.
- The prompt asks for a theorem, so the model turns branch-local data into
  theorem parameters.
- The target should be the local proposition
  `C (n + 1) = w * (y * C n * z) * w⁻¹`, not a new theorem quantifying over
  `n` and `ih`.

General fix:

- After every tactic that changes the goal shape, especially `induction`,
  rebuild the prose context from the returned metavariable's local context.
- For induction branches, include a branch header:

```text
Branch: successor case of induction on n
Branch variables:
  n : ℕ
  ih : l (C n) ≤ l s⁻¹ + l t + ↑n * (l y + l z)
Target:
  C (n + 1) = w * (y * C n * z) * w⁻¹
```

- Do not reuse the outer theorem's prose `Current goal` inside branch-local
  translation prompts.  If the outer theorem is useful, label it as
  `Enclosing theorem, not the target`.

Implementation site:

- `LeanAideCore/LeanAideCore/PaperCodes.lean`, at
  `TODO-InductionPromptContext` near the induction handler.

## Example 3: proof/tactic prompt target contains a stale theorem-shaped proposition

Source: `.logs/2026-07-28.log:25679`.

Prompt kind: **proof/tactic**, not translation.  Unlike Examples 1 and 2, this
prompt asks for a proof of a displayed Lean infoview goal.  The prompt template
is therefore mostly the right interface.  The problem is upstream: the goal
after `⊢` is theorem-shaped and stale before the model sees it.

The following is close to the full user prompt content for this tactic call,
apart from JSON logging wrappers:

```text
Solve this Lean 4 Infoview goal state.

Use the hypotheses and variables before `⊢` as the local context, and prove the
target after `⊢`. Produce a complete tactic proof starting with `by`. The proof
must elaborate without leaving any goals, and it must not contain `sorry`,
`admit`, generated placeholders, or explanatory text.

Goal state:
```lean
G : Type u_14
inst_14157295161945824867 : Group G
l : G → ℝ
a_8164486838467395441 : IsHomogeneousPseudoLength G ℝ l
w y z s t : G
C : ℕ → G := fun n => (w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n
n : ℕ
ih : l (C n) ≤ l s⁻¹ + l t + ↑n * (l y + l z)
⊢ have C := fun n => (w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n;
  ∀ (n : ℕ), l (C n) ≤ l s⁻¹ + l t + ↑n * (l y + l z) → C (n + 1) = w * (y * C n * z) * w⁻¹
```
```

The target is not the branch-local equality.  It has reintroduced `C`, `n`, and
the induction hypothesis implication under a new `∀`, even though `C`, `n`, and
`ih` are already in the local context.

A later proof/tactic prompt at `.logs/2026-07-28.log:38231` shows the good form
of the same interface:

```lean
G : Type u_14
inst_14157295161945824867 : Group G
l : G → ℝ
a_8164486838467395441 : IsHomogeneousPseudoLength G ℝ l
w y z s t : G
C : ℕ → G := fun n => (w * y) ^ n * s⁻¹ * t * (z * w⁻¹) ^ n
n : ℕ
ih : l (C n) ≤ l s⁻¹ + l t + ↑n * (l y + l z)
...
⊢ l (C (n + 1)) ≤ l s⁻¹ + l t + ↑(n + 1) * (l y + l z)
```

Diagnosis:

- The tactic prompt template is sound, but upstream target construction can
  still pass a stale theorem-shaped expression.
- This is a context/target boundary bug: local hypotheses have been duplicated
  into the target as new binders.

General fix:

- Before sending a tactic prompt, normalize the target against the current
  local context:
  - remove leading `let`/`have` binders whose declarations already exist in the
    local context,
  - specialize leading `∀` binders when a unique matching local declaration is
    available,
  - reject or repair targets that re-quantify a local induction variable and
    its `ih`.
- Add a prompt preflight check that compares the target after `⊢` with the
  active `MVarId` type.  If they differ, log both and do not call the LLM.

Implementation sites:

- `LeanAideCore/LeanAideCore/CodegenCore.lean`, where source propositions are
  converted into proof/tactic goals.
- `LeanAideCore/LeanAideCore/PaperCodes.lean`, where nested proof and assertion
  handlers decide whether to translate a proposition, prove a proposition, or
  call tactic search.

## Example 4: generated local facts are too generalized for later prompts

Source: `.logs/2026-07-28.log:127619`.

Prompt kind: **context rendering issue**, affecting both translation prompts and
proof/tactic prompts.  This is not itself a separate LLM request.  It is a slice
of the local-context block included in the Example 1 translation prompt.  The
local context sent to later prompts contains facts such as:

```lean
have assert_11251285474415531252 : have c := x * y * x⁻¹ * y⁻¹;
have f := fun m k => l (x ^ m * c ^ k);
∀ (m k : ℤ),
  have a := x ^ m * c ^ k;
  have w := x;
  have u := x ^ (m - 1) * c ^ k;
  have v := y⁻¹ * x ^ m * c ^ (k - 1) * x * y;
  l u = f (m - 1) k := ⋯
```

In the current branch, `m`, `k`, `u`, and `f` are already fixed.  The useful
fact is the specialized local statement:

```lean
have assert_11251285474415531252 : l u = f (m - 1) k := ⋯
```

Diagnosis:

- Generalized assertions make prompts longer and less aligned with the actual
  branch.
- They encourage the model to preserve or regenerate `∀ (m k : ℤ)` structure
  even when the goal is already specialized.

General fix:

- When adding generated assertions to prompt context, display the specialized
  local type if the proof step has already been introduced in the current local
  context.
- Hide proof terms and avoid displaying reconstructed `have`/`let` scaffolding
  inside the proposition unless it is genuinely part of the target.
- Prefer an `Available facts` block:

```text
Available facts:
assert_11251285474415531252 : l u = f (m - 1) k
assert_3328252475526390330 : y * v * y⁻¹ = x ^ m * c ^ (k - 1) * x
```

## Recommended prompt contract

Use separate contracts for each translation stage:

| stage | prompt should ask for | forbidden output |
|---|---|---|
| top-level theorem statement | a theorem/lemma/definition command | proofs unless explicitly wanted |
| local assertion proposition | a Lean proposition term only | `theorem`, `lemma`, `def`, `example`, `by` |
| local assertion proof | a `by ...` term/tactic proof for the exact target | new top-level declarations, restated theorem |
| tactic repair | a complete `by ...` proof for the displayed infoview goal | any changed target or added binders |
| nested proof block | proof steps for the active subgoal only | closing or restating the parent theorem |

Every prompt for a nested call should contain these named sections, in this
order:

```text
Task:
  <one sentence saying proposition-term, proof-term, tactic-proof, or command>

Available variables:
  <freshly generated from the active Lean local context>

Available facts:
  <specialized local facts only; no proof bodies>

Target:
  <the exact active target or exact proposition to translate>

Enclosing theorem, for orientation only:
  <optional, with proofs suppressed; never labelled Current goal>
```

The phrase `Current goal` should be reserved for the actual active `MVarId`
target.  If a larger theorem is included for context, call it `Enclosing
theorem` or `Outer theorem`, and explicitly say that it must not be proved or
restated.

## Concrete code changes to make

1. In `LeanAideCore/LeanAideCore/Translator.lean`, replace the single generic
   `Translate the following statement into Lean 4` wrapper with prompt builders
   keyed by translation mode.
2. In `LeanAideCore/LeanAideCore/PaperCodes.lean`, make `assertionCode` call a
   local-assertion proposition/proof prompt, not the theorem prompt.
3. In `LeanAideCore/LeanAideCore/PaperCodes.lean`, refresh `promptContext`
   after induction and case splits from the returned branch metavariable.  The
   existing `TODO-InductionPromptContext` is the right anchor.
4. In `LeanAideCore/LeanAideCore/PaperCodes.lean`, stop adding the enclosing
   theorem as `Current goal` for nested calls.  If retained, relabel it as
   `Enclosing theorem, not the target`.
5. In `LeanAideCore/LeanAideCore/CodegenCore.lean`, preflight every tactic LLM
   prompt by comparing the displayed target with the active goal type.  Do not
   call the LLM if the target re-quantifies local variables or contains stale
   wrapper `have` binders.
6. In local-context rendering, collapse assigned proof-valued facts to
   `name : type := ⋯`, with the type specialized to the current local context.
