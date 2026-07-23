# Generation check for `results/homogeneous.md`

## Update: July 23 corrected-goal and direct-validation rerun

### Completed run and confirmed behavior

The rebuilt executable contains both fixes under test:

1. `runForSingleGoal` now checks `mvar.isAssigned`, where `mvar` is the
   continuation goal returned by the tactic, instead of checking the expectedly
   assigned input goal `mvarId`.
2. The tactic branch of `let_statement` first calls
   `checkTacticsFromString` on the direct local tactic `let <name> ... :=
   <value>` in the actual goal context, accepts it only when it returns exactly
   one continuation goal, and falls back to `defStx` otherwise.

`lake build codegen` succeeded.  The fresh real-API run of
`lake exe codegen results/core-homogeneous.json` ran from 10:17:30 to 11:26:17
(lines 37,269--141,808 of `.logs/2026-07-23.log`) and exited 0.  It made 71 LLM
queries: 15 were served from the chat cache and 56 received fresh responses.
There was no API, LeanSearch, or similarity-server timeout in this run.

Both authorized artifacts were written and pass independent `lake env lean`
checks:

| Artifact | Lines | Declarations generated |
|---|---:|---|
| `CodeGen/Live/core-homogeneous.lean` | 374 | 4 definitions; Lemmas 1, 3, and 4 |
| `CodeGen/core-homogeneous.lean` | 644 | the same declarations plus final diagnostics |

The source has four definitions and four lemmas, so definition coverage is
complete but theorem coverage is only 3/4.  The live file has no `skip`, but it
has 11 occurrences of `repeat (sorry)`: one in Lemma 1, seven in Lemma 3, and
three in Lemma 4.  Thus the artifacts elaborate, but proof completion remains
poor.  The final diagnostic's later phrase `Sorries after purge: none` refers
to its diagnostic purge, not to the emitted declarations; the declarations
still contain those 11 sorries.

The corrected-goal fix is confirmed dynamically.  There is no occurrence of
`single generated goal is already assigned` or `no goals to be solved` in the
fresh trace, and generation advances through many continuation goals.  The
direct local-`let` validation is also confirmed: Lemma 4 emits the local
definitions of `a`, `w`, `u`, and `v`, including terms depending on the
earlier local `c`, and later prompts retain all four.  This is the case which
the old command-prelude validation rejected with `Unknown identifier c`.

### Lemma 2: a failed proof node currently drops the theorem

Lemma 2 reached its induction step, but at 10:34:03 translation of the local
assertion

```lean
C (n + 1) = w * (y * C n * z) * w⁻¹
```

failed with `no valid function found for key assert_statement`.  The enclosing
proof was then abandoned, so `lemma_2` is absent from
`CodeGen/Live/core-homogeneous.lean`; codegen continued with Lemma 3.  This is
not delayed output or buffering.

The required recovery has two distinct levels:

1. A failed intermediate JSON proof node must not abort the theorem.  In
   `getCodeTacticsAux` at
   `LeanAideCore/LeanAideCore/CodegenCore.lean:225-238`, the exception handler
   already restores `Term.State` and `Translate.State`, but then rethrows.
   The catch is currently inside `let code? ← ...`, so it cannot directly
   return the recursive function's pair.  Make this `try` return a tagged
   success/failure result (or move the catch around the whole per-source
   branch), then handle the failure arm with
   `getCodeTacticsAux translator goal sources accum`: keep the same unassigned
   goal and accumulated tactics, drop only the failed `source`, and try the
   remaining JSON nodes.  In schematic form:

   ```lean
   let result ← try
     let code? ← getCode translator (some goal) ``tacticSeq source
     termState.restore
     pure (.ok code?)
   catch e =>
     termState.restore
     set translateState
     pure (.error (← e.toMessageData.toString))
   match result with
   | .error _ => getCodeTacticsAux translator goal sources accum
   | .ok code? => -- existing handling of `code?`
   ```
2. If all remaining JSON nodes and final automation leave the goal open,
   `getCodeTactics` at
   `LeanAideCore/LeanAideCore/CodegenCore.lean:334-346` must append the terminal
   `repeat (sorry)` fallback to the accumulated tactics.  At present its
   `findTactics? = none` branch returns `tacs` unchanged; the resulting theorem
   command has an open goal and is discarded by the command-level handler.

This refines the earlier recommendation about `findTacticsI`: failed
per-assertion proof search should remain an explicit failure rather than
silently manufacturing a successful assertion, but the *outer proof
sequence*, after every structured source has been tried, should deliberately
close whatever remains with `repeat (sorry)`.  That preserves the translated
theorem and all later usable steps while making the incomplete proof explicit.
Regression tests should cover failure of the first, middle, and last proof
node, verify that later nodes are attempted, and verify that only the terminal
exhaustion path emits `sorry`.

Focused TODO comments marking both control-flow changes are now in
`CodegenCore.lean` as `TODO-ProofStepFailureContinue` and
`TODO-ProofExhaustionFallback`.

### Deeper issues exposed after the two fixes

1. **Local assertion translation is not sufficiently claim-specific.**  A
   requested local equality such as `w * u = a` is translated into a theorem
   universally quantifying the group, pseudo-length, points, exponents, and
   all local definitions.  More seriously, while translating Lemma 4's local
   claim `c = x*y*x⁻¹*y⁻¹`, the full-statement fallback accepted the
   *entire final recurrence theorem*.  This created
   `assert_16329814440308656878` with `repeat (sorry)` and allowed `grind` to
   close the theorem early.  The later JSON proof nodes were therefore never
   attempted.  `translateToPropStrict` must have a local-assertion mode which
   either disables the broad `server.fullStatement` fallback or validates
   that its result is a faithful reformulation of the requested claim, rather
   than merely any elaborating proposition from the surrounding prompt.
2. **Internal assertion proof search still manufactures success.**
   `findTacticsI` uses `repeat (sorry)` when `findTactics?` returns `none`.
   This explains all 11 sorry-backed local assertions.  Keep an assertion
   failure explicit so that the outer recovery can move to the next JSON node;
   use `repeat (sorry)` only once, at terminal proof exhaustion.
3. **Proof values bloat later prompts.**  Assigned proof-valued local
   declarations are rendered as `let name : Prop := <large kernel term>` by
   `localDeclContextLine?`.  Later Lemma 3 prompts reach roughly 17k--19.5k
   input tokens.  For a local declaration whose type is a proposition, render
   only its name and type; retain assigned values for data definitions such as
   `c`, `f`, `a`, `w`, `u`, and `v`, where the value is semantically needed.
4. **Existing local hypotheses are underused.**  For example, the assertion
   that `l` is a homogeneous pseudo-length should reuse the hypothesis already
   in the local context instead of translating and proving a new generalized
   theorem.  Before invoking the LLM, check whether the requested assertion
   directly elaborates in the goal context or matches an existing local
   hypothesis.
5. **Duplicate proof nodes are regenerated.**  The exact `w * u = a` claim
   appears twice and receives the same hash-based name.  Lean permits the
   resulting local shadowing, but it wastes translation and proof work.  The
   source audit should remove exact duplicate proof nodes, and codegen should
   avoid re-emitting an identical local proposition already in context.
6. **One universe-serialization defect remains.**  The trace has one
   `unknown universe level` occurrence for the already identified RHS-only
   `u_12` case.  Auto-implicit declaration headers do not bind a universe that
   first appears inside a serialized proposition value; the level-preserving
   serialization recommendation below remains necessary.

### Focused changes from the completed run

1. **P0 -- retain the theorem after a proof-step error:** change the catch in
   `getCodeTacticsAux` to return a failure marker after the existing state
   restoration, then recurse on `sources` with the original `goal` and
   `accum` from the result match.  A direct recursive call inside the current
   `let code?` catch has the wrong return type.
2. **P0 -- terminal proof fallback:** in the final `findTactics? = none`
   branch of `getCodeTactics`, use
   `appendTacticSeqSeq tacs (← \`(tacticSeq| repeat (sorry)))`.  Do not place
   this fallback inside assertion proof search.
3. **P0 -- assertion relevance:** give `translateToPropStrict` a constrained
   local-assertion path; do not accept an enclosing theorem as the translation
   of a small local claim.
4. **P0 -- explicit assertion failure:** replace `findTacticsI` at assertion
   call sites by an option/error path so the outer proof sequence can recover.
5. **P1 -- concise proof context:** change `localDeclContextLine?` to omit the
   assigned value when the declaration type is `Prop`, while preserving values
   for non-proof local lets.
6. **P1 -- coverage accounting:** record attempted and failed JSON proof-node
   identifiers.  A theorem may close legitimately before all proof nodes, but
   early closure caused by a mistranslated assertion must be reported rather
   than silently counted as success.

## Update: July 23 auto-implicit and `let`/`def` quick-fix rerun

### Changes checked

The two quick fixes under test are present in the rebuilt executable:

1. `elabFrontTheoremExprWithCommandPreludeM` now checks temporary theorem
   declarations with `autoImplicit true`.
2. `translateDefCmdM?` rewrites a candidate beginning with `let ` to begin
   with `def ` before parsing it as a command.

A search found two other production theorem wrappers which still explicitly
disabled auto-implicits, `elabFrontTheoremExprMStrict` and
`elabFrontTheoremExprM` in `LeanAideCore/LeanAideCore/SimpleFrontend.lean`.
Both now use `autoImplicit true`. The remaining `autoImplicit false`
occurrences are standalone old examples and `LeanAideTest` inputs, not codegen
wrappers, so they were not changed. `lake build codegen` succeeded after all
three wrapper changes.

I then ran:

```bash
lake exe codegen results/core-homogeneous.json
```

The run lasted from 09:11:51 to 09:13:53, exited 0, and wrote both authorized
output files. Its trace is the part of `.logs/2026-07-23.log` beginning at line
28,402 and ending at line 37,268. There were 20 OpenAI query attempts: 18 were
served by the existing response cache and two were cache misses. There was no
timeout. Both generated files pass independent `lake env lean` checks.

The artifacts are byte-for-byte unchanged from the preceding quick-fix run:
four definitions and no theorems. Thus process success still masks incomplete
source coverage.

### The auto-implicit fix works, but only at declaration headers

The temporary wrapper now accepts `Type*`, generalizes it to `u_12`, and
successfully returns the translated proposition. More importantly, the
assertion candidates for Lemmas 1--3 containing `Type u_12` now elaborate and
enter proof generation. The fresh trace has only one `unknown universe level`
error, compared with 89 in the preceding run.

The one remaining failure is the already identified RHS-only case:

```lean
def core_homogeneous_root_homogeneity_square.prop : Prop :=
  ∀ (G : Type u_12), ...
```

Because `u_12` first occurs in the value rather than the declaration header,
`autoImplicit` does not bind it. The proper level-parameter preservation and
dynamic universe-prelude fix is therefore still required for serialized
propositions and final code.

### Newly exposed blocker: `runForSingleGoal` checks the wrong goal

All four lemmas now reach their first structured tactic. Each tactic makes
ordinary progress and returns one continuation goal. For example, Lemma 1
runs a tactic of the form:

```lean
have h : l (y * x * y⁻¹) ≤ l x := by ...
```

Lean assigns the original goal to a proof term containing the new continuation
metavariable and returns that new metavariable. This is normal tactic behavior.
However, the one-goal branch in
`LeanAideCore/LeanAideCore/RunTactics.lean:153-157` currently says:

```lean
| [mvar] =>
  if ← mvarId.isAssigned then
    throwError "single generated goal is already assigned ..."
```

Here `mvarId` is the original goal, which is expected to be assigned after a
successful non-closing tactic. The check must inspect the returned goal:

```lean
if ← mvar.isAssigned then ...
```

and then commit the returned tactic state and return `mvar`. The input check at
line 138 is valid, and the empty-list branch already represents a tactic which
closed the goal. The fresh log contains four independent failures at this
point, repeated by higher-level error reporting to give 12 textual occurrences
of `single generated goal is already assigned`.

This refines the older state-leak diagnosis below for the current code.
`withoutModifyingTranslateAndTermState` now saves both `Translate.State` and
`Term.SavedState`; Lean's `Term.SavedState` includes `Meta.SavedState`, so an
additional Meta field is not needed there. `runForSingleGoal` also saves its
term state and restores it in the exception path. The immediate current
failure is the old-goal/new-goal identity mistake, not a failure to save Meta
state.

There is a second issue in the same example. `assertionCode` obtains its proof
tactics through `findTacticsI`, whose no-result default is still:

```lean
repeat (sorry)
```

Consequently, changing `mvarId` to `mvar` would allow generation to proceed,
but initially with sorry-filled local assertions. Required proof search must
return an explicit failure when `findTactics?` returns `none`; `sorry` should
not be an internal success value.

### What the `let` to `def` rewrite did

Lemma 4 exercised the rewrite. The model returned the appropriate local
candidate

```lean
let a : G := x ^ m * c ^ k
```

and `translateDefCmdM?` rewrote it to:

```lean
def a : G := x ^ m * c ^ k
```

This removed the command-parser mismatch, but semantic validation still
rejected the command. The prompt's local context contained the claim-local
definitions of `c` and `f`, while the frontend validation prelude reconstructed
only `G`, its instance, `l`, `x`, `y`, `m`, and `k`. The cached frontend error
is exactly `Unknown identifier c`.

After all eight rewritten candidates were rejected, `defStx`'s structured
fallback and `commandToTactic` nevertheless produced the correct local tactic:

```lean
let a : G := x ^ m * c ^ k
```

That tactic executed and returned its continuation goal, then hit the same
incorrect `mvarId.isAssigned` check. Therefore the rewrite is useful as a
top-level command normalization, but is not the generic solution for local
`let_statement` nodes. Local definitions should translate/validate the
structured `value` as a term in the actual goal context and construct a local
`let` tactic directly. If command-based validation is retained, its prelude
must preserve local let-declarations such as `c` and `f`.

### Focused TODOs from this run

1. **P0 -- returned-goal check:** in `runForSingleGoal`, test the returned
   `mvar`, not the assigned input `mvarId`; add regression tests for a tactic
   that returns one continuation (`have`/`let`) and a tactic that closes the
   goal.
2. **P0 -- explicit proof-search failure:** replace `findTacticsI`'s
   `repeat (sorry)` default with an explicit no-proof result and propagate it
   through assertion and nested-proof generation.
3. **P0 -- universe closure:** retain generalized level parameters and emit a
   dynamic universe prelude for proposition values and final serialization;
   header auto-implicits alone cannot fix the `.prop : Prop := ...` form.
4. **P1 -- local definitions:** bypass the top-level definition translator for
   tactic-sequence `let_statement` nodes, or preserve local let-declarations in
   the validation context. Keep the `let` to `def` rewrite scoped to actual
   command translation.
5. **P0 -- required-source coverage:** an exit-0 file with four of nine
   required declarations must be reported as partial/failure, while
   prompt-only `assume_statement` nodes remain exempt.


## Update: July 23 quick-fix rerun

### Changes made and run result

For this diagnostic rerun I changed only `results/core-homogeneous.json`:

1. Definition 8 was rewritten from an equivalence-shaped sentence to an
   explicit introduction of the requested name:

   ```text
   Define IsTorsionFree (A) for an abelian group A to mean
   AddCommGroup.torsion A = ⊥.
   ```

2. Each of the five `let_statement` nodes now has an explicit `statement`
   field beginning with `Define`: the `z` in Lemma 1 and the `a`, `w`, `u`,
   and `v` in Lemma 4. The structured `value` fields were left unchanged.

I then ran the rebuilt current executable with real API calls:

```bash
lake exe codegen results/core-homogeneous.json
```

The run lasted from 07:54:37 to 08:09:58, exited 0, and wrote both
`CodeGen/Live/core-homogeneous.lean` and
`CodeGen/core-homogeneous.lean`. The fresh trace is the portion of
`.logs/2026-07-23.log` beginning at line 14,673; the file now has 28,401
lines. There were 16 model responses in the fresh trace and no timeout. Both
generated files also pass an independent `lake env lean` check.

That successful process status still overstates the semantic result:

| semantic source kind | in JSON | emitted before rerun | emitted now |
|---|---:|---:|---:|
| definitions | 4 | 3 | 4 |
| theorems | 5 | 0 | 0 |
| total declarations | 9 | 3 | 4 |

The only new mathematical declaration is `IsTorsionFree`. The final file has
no theorem, `sorry`, or `skip`; this is because all five theorems were omitted,
not because their proofs were completed. The four string-literal `#check`
commands remain diagnostics rather than declarations.

### Definition 8 workaround succeeded

The explicit definitional wording fixed the command-kind ambiguity. All eight
fresh candidates were actual definitions, for example:

```lean
def IsTorsionFree (A : Type _) [AddCommGroup A] : Prop :=
  AddCommGroup.torsion A = ⊥
```

The first valid candidate elaborated, `defCode` reported success, and the
definition appears in both output files. This supports the generic upstream
recommendation already made below: definition nodes should be audited and
rewritten to introduce their requested name explicitly. It was not a
torsion-specific Lean repair.

### Why `Type*` became the new universe `u_12`

The `u_11` quick fix did not merely miss one more name. It exposed why a fixed
list cannot solve this problem.

The theorem claims contain syntax such as:

```lean
∀ (G : Type*) [Group G], ...
```

`Type*` (equivalently, in this respect, `Type _`) asks Lean to create a fresh
universe metavariable; it does not select an existing declared universe.
`elabFrontTheoremExprWithCommandPreludeM` in
`LeanAideCore/LeanAideCore/TheoremElabCheck.lean:26` embeds the candidate in a
temporary declaration:

```lean
noncomputable def my_shiny_new_theorem : <candidate> := by sorry
```

When elaborating a declaration, Lean calls `Term.levelMVarToParam` to
generalize an unresolved universe metavariable. That function deliberately
chooses the first unused name of the form `u_i` relative to the current level
names. The artificial frontend prelude now declares `u_1` through `u_11`, so
the fresh parameter is correctly named `u_12`. Adding `u_12` would make the
next placeholder become `u_13`.

The information is then lost at
`LeanAideCore/LeanAideCore/TheoremElabCheck.lean:39`, which returns only
`seek.type`. The temporary declaration's `seek.levelParams` are not retained.
Delaboration prints the parameter as `u_12`, and later frontend checks reparse
that text using a prelude declaring only through `u_11`; they consequently
report `unknown universe level 'u_12'`. The fresh log has 89 occurrences of
that diagnostic. It rejects the homogeneity-square command and the otherwise
plausible first assertion candidates in Lemmas 1--3.

The proper fix is to preserve universe closure as part of the elaboration
result. For example, return an `ElaboratedType` containing the `Expr` and its
level parameters (using `seek.levelParams`, or collecting parameters from the
expression). Whenever that expression is delaborated and reparsed, prepend a
dynamically generated `universe ...` command for exactly those parameters; do
the same in final emitted top code. Alpha-normalizing the retained parameter
names is reasonable, but their sharing and level expressions must be
preserved. Unifying the three existing fixed lists is still useful to prevent
configuration drift, but is not by itself a fix for `Type*`.

As a smaller interim change, register every returned `seek.levelParams` name
in the command prelude and emitted top data before rechecking the delaborated
expression. This will fix the immediate unknown-name failure, although the set
will grow as further `Type*` declarations are generalized.

There is also a narrower built-in fix for declaration headers. Lean's
`autoImplicit` option covers named universe levels as well as term variables,
and its default is `true`; importing Mathlib does not turn it off. This was
verified against the repository's Lean 4.28 toolchain. LeanAide explicitly
overrides the default with `set_option autoImplicit false in` in
`TheoremElabCheck.lean:31` and in the analogous helpers at
`SimpleFrontend.lean:171` and `SimpleFrontend.lean:185`. Removing those
overrides, or changing them to `true`, lets a header such as

```lean
noncomputable def candidate :
    ∀ (G : Type u_12), P G := by sorry
```

auto-bind `u_12`. This should remove the repeated candidate-checking failures
where the level occurs in the temporary declaration header.

It is not a complete replacement for universe closure. Auto-implicit universe
binding applies to declaration headers, not to a universe first mentioned only
in a definition value. The generated homogeneity-square command has exactly
the latter shape:

```lean
def core_homogeneous_root_homogeneity_square.prop : Prop :=
  ∀ (G : Type u_12), ...
```

and still needs an explicit/dynamic universe declaration, explicit declaration
level parameters, or a representation that puts the proposition in the
declaration's type. Therefore re-enable `autoImplicit` for the temporary
frontend wrappers as the immediate fix, while retaining level parameters for
RHS-only serialization and final output.

### Changing `let` to `Define` did not fix local definitions

Lemma 4 reached the first patched step and sent the model both

```text
Define a to be x^m * c^k.
Define ONLY the term a with value x^m c^k.
```

All eight candidates nevertheless returned the locally appropriate syntax:

```lean
let a : G := x ^ m * c ^ k
```

They were all rejected with `expected command`. This is an interface mismatch,
not a failure to understand the mathematical definition:

- the tactic-sequence branch of `letCodeCore` at
  `LeanAideCore/LeanAideCore/PaperCodes.lean:678` calls `defStx` and then
  `commandToTactic`;
- `defStx` calls `translateDefCmdM?`, which parses every candidate in Lean's
  top-level `command` category;
- a local `let` is a tactic/term construct, not a top-level command, so the
  parser rejects it before `commandToTactic` can run.

The corresponding fallback handler in `LeanAide/PaperCodes.lean` has the same
shape. Since the first `a` step failed, the run did not reach the patched `w`,
`u`, or `v` steps. Lemma 1 did not reach its patched `z` step because its first
assertion had already failed on `u_12`. Thus only `a` was directly tested, but
all five nodes share the same structural defect.

The robust fix is to split local and top-level definition handling. In a
`tacticSeq`, use the structured `variable_name` and optional `variable_type`,
translate only `value` as a term in the current goal context, and construct a
local `let` tactic directly. Alternatively, accept and validate candidates in
the `tactic` category. Keep `translateDefCmdM?` plus `commandToTactic` only for
top-level `commandSeq` definitions. A prompt demanding the literal token
`def` would be a brittle workaround: the model's `let` is exactly the syntax
appropriate to the context.

### Other behavior confirmed by the deeper run

- `assume_statement` again produced 58 `returned : false` events. These are
  successful prompt-only updates, not omissions.
- The restarted similarity service did not time out. The fallback
  `LeanAideUrl` synthesis message remains noisy but was not causal.
- Each of Lemmas 1--4 ran a broad whole-goal automation sweep before its
  supplied structured proof steps. The entry point is
  `getCodeTactics` at `LeanAideCore/LeanAideCore/CodegenCore.lean:307`, which
  calls the full `findTactics?` suite before inspecting `sources`. In this run
  those four sweeps were expensive and found no proof. When structured steps
  exist, first try only cheap deterministic closure (`assumption`, exact,
  tightly bounded simplification), process the steps, and reserve broad
  `hammer`/LLM automation for the remaining goal.
- Codegen again returned success after omitting every required theorem. The
  source-coverage failure described below remains a P0 issue.

### Focused TODOs from this rerun

No Lean source was changed in this quick-fix experiment. The next Lean changes
should be:

1. **P0 -- restore header universe auto-implicits and carry parameters:** remove
   the three local `autoImplicit false` overrides used by temporary frontend
   declarations. Also return theorem expressions with their level parameters
   and add an exact dynamic universe prelude for RHS-only serialization and
   final output. Regress both a header-level `u_12` and a `Type*` proposition
   stored as the value of a `def : Prop`.
2. **P0 -- required-source coverage:** make exit status/final reporting fail or
   say `partial` for any theorem or definition without a committed declaration,
   while exempting prompt-only assumptions.
3. **P1 -- direct local-let path:** construct/validate a local tactic from the
   structured node and translate only its value as a term; do not require a
   top-level command as an intermediate representation.
4. **P1 -- proof-search ordering:** do not run the broad automation suite ahead
   of nonempty structured proof steps; retain a cheap closure check and defer
   expensive fallback automation.
5. **P1 -- retain the generic definition-intent audit:** the Definition 8
   experiment is now a passing regression for explicit definitional wording.


## Update: July 23 `core-homogeneous.json` codegen run

### Run and headline result

I ran

```bash
lake exe codegen results/core-homogeneous.json
```

after allowing Lake to rebuild the current `codegen` executable and its
dependencies. The run used the configured real OpenAI backend and the restarted
local similarity server. It completed with exit status 0 and wrote both
authorized artifacts:

- `CodeGen/Live/core-homogeneous.lean`;
- `CodeGen/core-homogeneous.lean`.

The detailed trace is `.logs/2026-07-23.log` (14,672 lines). Process success is
not semantic success in this run. The input has four top-level definitions and
five top-level theorems, while the final file has only three declarations:

| semantic source kind | in JSON | emitted | omitted |
|---|---:|---:|---:|
| definitions | 4 | 3 | 1 |
| theorems | 5 | 0 | 5 |
| total declarations | 9 | 3 | 6 |

The surviving declarations are `PseudoLength`, `IsLength`, and
`IsHomogeneousPseudoLength`. Definition 8 (`IsTorsionFree`), the derived
homogeneity-square claim, and Lemmas 1--4 are absent. The four lookup nodes were
also emitted, but only as `#check` commands on string literals; they are not
declarations and do not validate the named constants.

The final elaboration report says `Sorries: none`, but this is vacuous evidence
about proof completion: every theorem was omitted before final elaboration. The
clean 44-line final file is therefore a safely filtered but severely incomplete
artifact.

### What worked

1. **The latest code was built and used.** Lake rebuilt the current dependency
   graph and `codegen` executable before starting generation.
2. **The first three definitions translate and elaborate.** Their requested
   JSON names are now preserved, unlike the older run's substitutions such as
   `IsPseudoLengthFunction`.
3. **The strict-`Prop` boundary is working for theorem claims.** All five theorem
   claims were translated to propositions. In particular, the translator
   repaired the stale JSON spelling `IsHomogeneousPseudoLength G l` to the
   actual one-argument application `IsHomogeneousPseudoLength l`.
4. **Top-level command commits are safer.** The universe-invalid claim command
   was not written to either generated file. This avoids the malformed,
   `skip`-heavy output of the older run, although the rejection is currently
   hidden by an incorrect overall success result.
5. **Prompt-only assumptions behaved as intended.** The log contains 58 events
   of the form

   ```text
   LeanAide.assumeCode for key assume_statement worked; returned : false
   ```

   These are not failures. `getCode` explicitly uses `none` for a successful
   side-effect-only handler. The assumptions were added to subsequent prompt
   context, and later prompts show the expected `G`, group instance, `l`, and
   local variables. There is no actual `assume_statement` error in this run.
   Failure accounting must distinguish `returned : false` from a thrown error
   or an explicitly required command that was not emitted.
6. **The similarity server was used without a timeout.** There are no `timeout`,
   `timed out`, or `leansearch` timeout messages in the fresh log. There are 17
   similarity-query events. The repeated message about failing to synthesize
   `LeanAide.LeanAideUrl` is followed by a successful fallback to the local
   server; it is configuration noise, not evidence that retrieval failed.

### Primary failure: generated universe `u_11` is not declared

Every translated theorem claim has a type beginning like

```lean
∀ (G : Type u_11) [inst : Group G] ...
```

For example, the homogeneity-square statement was translated correctly to

```lean
∀ (G : Type u_11) [inst : Group G] (l : G → ℝ),
  IsHomogeneousPseudoLength l →
  ∀ (g : G), l (g ^ (2 : ℤ)) = (2 : ℝ) * l g
```

but its fallback claim command was rejected as

```lean
def core_homogeneous_root_homogeneity_square.prop : Prop :=
  ∀ (G : Type u_11) [inst : Group G] ...
```

with

```text
error: unknown universe level `u_11`
```

The same error appears in otherwise plausible assertion candidates for Lemmas
1--3. There are 88 occurrences of this diagnostic in the log.

This is a deterministic internal mismatch, not an LLM translation error:

- `LeanAideCore/LeanAideCore/TheoremElab.lean:13` includes `u_11` in
  `levelNames`, so theorem elaboration is allowed to produce an expression with
  that named universe.
- `LeanAideCore/LeanAideCore/ConfigExts.lean:17` declares only through `u_10` in
  the generated top code.
- the default frontend prelude in
  `LeanAideCore/LeanAideCore/SimpleFrontend.lean:14` also declares only through
  `u_10`.
- `delabDetailed` then faithfully prints the expression's `u_11`, and the
  command checker sees an undeclared level.

Merely adding `u_11` in one string would fix this instance but leave the three
lists able to drift again. The robust change is to have theorem elaboration,
frontend checking, and emitted top code share one universe policy. Either
normalize generated level parameters to a known declared set, or collect the
level parameters from accepted expressions and emit the corresponding
`universe` command. At minimum, `levelNames`, `topCodeData`, and the default
`simpleRunFrontend` prelude must be generated from one source of truth.

This bug also wasted proof calls. The system continued asking the model for
alternatives even though each candidate was being checked in a context that
could not parse its universe. Validate universe closure and the complete
candidate prelude once before launching proof search.

### Per-item result

| item | statement translation | proof/code result |
|---|---|---|
| Definitions 1--3 | Successful, with requested names | Emitted and elaborated |
| homogeneity-square | Correct proposition, including corrected application of `IsHomogeneousPseudoLength` | Generated `.prop` command rejected solely because `u_11` was undeclared, then silently omitted |
| Definition 8 | Mathematical content recognized | All eight candidates were theorem commands, not a definition of `IsTorsionFree`; definition handler rejected them and the existential fallback also failed |
| Lemma 1 | Correct conjugation-invariance proposition | First substantive assertion candidates were rejected because they contained `u_11`; theorem omitted |
| Lemma 2 | Correctly includes the finite definition of `C` in the claim | Base-case assertion candidates were rejected because they contained `u_11`; theorem omitted |
| Lemma 3 | Correctly includes both conjugacy witnesses as hypotheses | Power-identity assertion candidates were rejected because they contained `u_11`; theorem omitted |
| Lemma 4 | Correctly includes `c` and `f` as claim-local definitions | Proof reached the first structured local definition, then rejected a valid local `let` as “expected command”; theorem omitted |

Thus the log does not establish that the mathematical proofs of Lemmas 1--4
failed. Lemmas 1--3 were stopped by the universe/checking defect before useful
proof completion could be assessed. Lemma 4 was stopped by a local-syntax
translation defect. No fresh `skip` or “no goals to be solved” issue appears in
this run.

### Definition 8 is phrased as a theorem, not a definition

The source node is labelled `definition`, named `IsTorsionFree`, and says:

```text
For an abelian group A, A is torsion-free iff T(A) = {0}.
```

All eight model candidates instead had the form

```lean
theorem AddCommGroup.isAddTorsionFree_iff_torsion_eq_bot :
  ∀ (A : Type u_1) [AddCommGroup A],
    IsAddTorsionFree A ↔ AddCommGroup.torsion A = ⊥ := by sorry
```

These are reasonable translations of the English sentence as an equivalence
theorem, but they cannot satisfy `defCode`, which correctly requires a `def` or
`noncomputable def` command and must preserve the requested name. The expensive
“There exists IsTorsionFree such that ...” fallback then attempted to prove the
equivalence and still could not recover a definition.

The generic upstream fix is to audit definition nodes for definitional shape.
A predicate-definition item with a requested name should be rewritten into an
explicit introduction, for example:

```text
Define IsTorsionFree (A) for an abelian group A to mean
AddCommGroup.torsion A = ⊥.
```

This should produce something like

```lean
def IsTorsionFree (A : Type u) [AddCommGroup A] : Prop :=
  AddCommGroup.torsion A = ⊥
```

If the intended content is instead the equivalence with Mathlib's existing
`IsAddTorsionFree`, the node should be classified as a theorem. This must be a
generic definition-intent audit, not a special case for torsion. On the Lean
side, `defCode` should report a command-kind mismatch immediately and should
not start existential proof search when every candidate is a theorem command.

### Lemma 4: local `let` is sent through a command translator

The relevant JSON step is already well structured:

```json
{
  "type": "let_statement",
  "variable_type": "G",
  "variable_name": "a",
  "value": "x^m c^k"
}
```

The model returned the locally valid syntax

```lean
let a : G := x ^ m * c ^ k
```

but `letCodeCore` calls `defStx`, which invokes `translateDefCmdM?` and parses
the result in the `command` category. The result was therefore rejected with
`expected command`. The implicated paths are
`LeanAideCore/LeanAideCore/PaperCodes.lean:676` and
`LeanAide/PaperCodes.lean:107`, especially the calls through `defStx` at lines
695--698 and 129--132 respectively.

For a tactic-sequence `let_statement`, translate the value as a term in the
current goal context and construct the local `let`/`have` syntax directly.
Command translation is appropriate only for document-level definitions. This
also avoids asking an LLM to reproduce the already structured variable name and
type.

### Silent omission is incorrectly reported as success

`getCodeCommands` in `LeanAideCore/LeanAideCore/CodegenCore.lean:345` catches a
source exception and continues, treats `none` as an unconditional continue,
and pushes even an empty result from `runAndCommitCommands`. In the
homogeneity-square case, `runAndCommitCommands` in
`LeanAideCore/LeanAideCore/TranslateM.lean:326` returns an empty array after the
only command fails frontend checking, but no required-source failure is
recorded. `leanFromStructuredJsonTask` consequently returns `"success"`, and
`codegen.lean:140` accepts that result because the three surviving declarations
elaborate.

Codegen needs structured per-source accounting with at least these outcomes:

- prompt/context-only success (for example `assume_statement` returning
  `none`);
- emitted and committed command;
- deliberately non-code document node;
- rejected/failed required semantic item.

The final status must be `partial` or `error` when a theorem or definition
produces no committed declaration. `codegen.lean` should compare required
semantic source IDs/names with committed declarations before writing an exit-0
final result. Best-effort live output can still be written, but it must not turn
six omissions into success.

### Diagnostic `#check` nodes still check only strings

`checkCode` in `LeanAideCore/LeanAideCore/PaperCodes.lean:261` looks up each
declaration and renders a description into a string literal, then emits
`#check "..."`. Lean therefore proves only that the literal has type `String`.
The four resulting “elaboration logs” are not declaration checks and should not
be counted as generated mathematical code. Put lookup information in a comment
or structured report field; if executable checking is wanted, emit
`#check commutatorElement`, not
`#check "commutatorElement has type ..."`.

### Similarity-server status

The restarted server removed the earlier operational blocker: no retrieval
timeout occurred. The fresh log nevertheless prints the missing
`LeanAide.LeanAideUrl` fallback message 51 times for 17 similarity queries.
Configure one local URL instance at startup, or make “use local server” an
explicit mode, so each query does not first fail dependency synthesis and emit
three noisy messages. This is a performance/diagnostic cleanup, not the cause
of the theorem omissions.

### Comparison with the earlier `CodeGen/homogeneous.lean`

The earlier full generated file is 1,675 lines and contains 15 declaration
headers, 108 textual `sorry` occurrences, and 31 `skip`s. Its early core portion
emits more declarations, but several are wrong: Definitions 2 and 3 became
theorems returning `Prop` with trivial `True` bodies; the Lemma 2 statement
accepts an arbitrary `C` instead of defining it; Lemma 3 drops essential
conjugacy hypotheses; and Lemma 4 is stated for an arbitrary `f`.

The fresh core JSON and statement translations are materially better:

- requested names and the first three definitions are preserved;
- `C`, the conjugacy hypotheses, and `c`/`f` now occur directly in the formal
  claims;
- rejected commands are not written, so there are no fresh `skip`s or
  `sorry`s.

The tradeoff is that the new final file hides nearly all substantive work. It
is cleaner than the earlier file but much less complete: three valid
definitions and zero theorems are not a successful generation of the nine
semantic items in the core input.

### Focused TODOs from this run

No Lean source was modified during this run, as requested. The following are
the focused implementation targets to add when Lean changes are next allowed:

1. **P0 — universe closure:** unify `TheoremElab.levelNames`,
   `ConfigExts.topCodeData`, and `SimpleFrontend.simpleRunFrontend` under one
   universe policy; add a regression using `Type*` that currently yields
   `u_11`.
2. **P0 — required-source coverage:** make `getCodeCommands` and
   `runAndCommitCommands` return structured outcomes, and make
   `leanFromStructuredJsonTask`/`codegen.lean` fail or report partial success
   when any theorem or definition has no committed declaration. Explicitly
   exempt prompt-only `assume_statement` nodes.
3. **P0 — preflight before proof calls:** validate the complete frontend
   prelude and universe declarations once before requesting proof candidates;
   do not spend further API calls on a deterministic context error.
4. **P1 — local-let translation:** in both `letCode` handlers, translate
   `value` as a term and build local syntax directly for `tacticSeq`; reserve
   `translateDefCmdM?` for `commandSeq`.
5. **P1 — definition-intent audit:** add a generic Python quality pass that
   ensures a node classified as `definition` introduces its requested name and
   has a definitional right-hand side; reclassify equivalence propositions as
   theorems. Add Definition 8 as a regression fixture.
6. **P1 — definition fallback:** when all returned candidates are theorem
   commands, report a definition/theorem kind mismatch instead of launching the
   existential-definition proof fallback.
7. **P2 — real checks:** replace string-literal `#check` commands with
   structured diagnostics or executable checks of the actual identifiers.
8. **P2 — local similarity configuration:** install an explicit local
   `LeanAideUrl`/mode once, avoiding repeated synthesis-failure fallback logs.
9. **P3 — codomain semantics:** decide whether the three length predicates are
   intended only over `ℝ`. If they are genuinely generic in `R`, replace the
   unrelated `[Zero R] [Add R] [LE R] ...` assumptions with the minimal
   law-bearing ordered additive structure needed by the definitions.

## Update: July 20 partial live codegen run

### Scope and outcome

This update analyses the supplied partial output
`CodeGen/Live/homogeneous.lean`, `.logs/2026-07-20.log`, the current
`results/homogeneous.json`, and the current implementations under
`LeanAideCore/` and `LeanAide/`. I also compiled both the live file and the
earlier `CodeGen/homogeneous.lean` independently.

The JSON contains five top-level definitions and fifteen top-level theorems.
The live file committed:

- all five definitions;
- Lemmas 1--4;
- a declaration named `lemma_6`, but not the statement of Lemma 6;
- Proposition 7 and Lemmas 8--11;
- Lemma 13.

Lemma 5 and Lemma 12 failed statement translation and were omitted. The live
file was last written at 14:26:59, after Lemma 13 was committed. The log
continued until 14:38:31 while Theorem 14 and its proof steps were being
processed, but Theorem 14 was never committed to the live file. Corollary 15
was not reached as a top-level command. Thus the live file is an incremental,
partial artifact, not the generated document returned by a successful
`runCodegen` call.

An independent check with

```bash
lake env lean CodeGen/Live/homogeneous.lean
```

fails. The decisive diagnostics are:

```text
line 234: AddConstAsyncResult.commitConst:
          constant has level params [u, v] but expected [u]
line 336: No goals to be solved
line 459: expected ';' or line break
line 459: Function expected at `sorry`
line 455: unsolved goals in lemma_13
```

The file contains 105 textual occurrences of `sorry` and 165 `skip` tactics.
Every emitted top-level theorem either contains a `sorry` or fails elaboration;
there is no completed top-level proof in this partial output. Because the first
syntax corruption in `lemma_13` occurs at line 459, the compiler cannot be
used as evidence that the remaining 969 lines of that proof are valid.

### What worked

The most important improvement over the earlier run is that the frontend-cache
context fix recommended below has now been implemented. In the current code:

```lean
checkElabFrontM (← withCommandPrelude s) (← cmdPreludeBlob).hash
```

passes an environment/prelude hash into the frontend cache key. This prevented
the stale `Unknown identifier IsPseudoLengthFunction` result seen in the July
4--5 run. All five foundational definition bodies now elaborate:

```lean
def IsPseudoLengthFunction ...
def IsLengthFunction ...
def IsHomogeneousPseudoLengthFunction ...
def commutatorOf ...
def AddCommGroup.IsTorsionFree ...
```

The main theorem statements through Lemma 11 are also substantially more
faithful than in `CodeGen/homogeneous.lean`:

- Lemma 1 now assumes a homogeneous pseudo-length function.
- Lemma 2 defines the term being bounded instead of quantifying over an
  arbitrary function `C`.
- Lemma 3 includes the two conjugacy hypotheses needed for its conclusion.
- Lemma 4 expands `f(m,k)` in terms of `l`, `x`, and the commutator instead of
  asserting the convexity inequality for every arbitrary `f : ℤ → ℤ → ℝ`.
- Proposition 7 and Lemmas 8--10 now carry the homogeneity/pseudo-length
  hypotheses that were absent in the earlier file.
- Lemma 9 now includes both factorization and preservation of the homogeneous
  pseudo-length axioms.
- Lemma 11 is emitted; it was absent from the earlier file.

There is also useful proof material among the failures. Examples include the
conjugation and power algebra in Lemmas 1--4, the construction of a function on
the abelianization and its uniqueness in Lemma 9, and the finite-torsion
calculation in Lemma 11. These fragments should be retained when repairing the
proofs, but they do not currently form complete declarations.

### Per-item translation and proof status

| JSON item | July 20 translation | Proof/elaboration result |
|---|---|---|
| Definitions 1--4, 8 | Mathematically reasonable bodies; all elaborate | Successful definitions, but the requested JSON names are not preserved |
| Lemma 1 | Corrected statement with homogeneity hypothesis | Two `sorry` blocks; useful conjugation argument around them |
| Lemma 2 | Corrected explicit formula for `C n` | Two `sorry` blocks, including the base case and conjugation-invariance step |
| Lemma 3 | Corrected conjugacy hypotheses | Four `sorry` blocks; the asymptotic/division argument is not completed |
| Lemma 4 | Corrected specialization of `f` | Three `sorry` blocks and many discarded prose steps (`skip`) |
| Lemma 5 | No command emitted, despite valid finite-sample candidates | Prose-only `f`/`S2n` made the prompt fragile, but the decisive failure is in candidate checking: newlines are flattened, arbitrary line subsets are tried, and a recovered `sorry` fragment aborts the loop before later valid candidates |
| Lemma 6 | Semantically wrong declaration | Emitted as `noncomputable def lemma_6 : ... → Prop := ... True`, not as the Rademacher estimate |
| Proposition 7 | Correct top-level statement | Three `sorry` blocks and a proof-only universe `v`, causing the `[u,v]` versus `[u]` commit error |
| Lemma 8 | Correct top-level statement | One `sorry`; does not implement induction/generation of the commutator subgroup |
| Lemma 9 | Correct top-level statement | Seven `sorry` blocks; a fallback `repeat sorry` closes the main goal at line 335, so the following `have` at line 336 produces `No goals to be solved` |
| Lemma 10 | Correct top-level statement | One `sorry`; this should be a short direct torsion/homogeneity proof |
| Lemma 11 | Correct factorization statement | Three `sorry` blocks; the local proof that torsion lies in the kernel is a useful completed fragment |
| Lemma 12 | No command emitted | `VQ` and `normQ` remain prose-level names in rejected candidates, leaving a `sorry`/metavariable in the translated type |
| Lemma 13 | Plausible top-level statement | Malformed generated syntax, 79 `sorry` occurrences, 130 `skip`s, unresolved `?m.*`, circular use of `lemma_13`, and repeated false or underspecified subclaims |
| Theorem 14 | Translation/proof generation started | No command committed before interruption |
| Corollary 15 | Not reached as a top-level item | No result in the live file |

### Translation failures

#### 1. `translateToPropStrict` does not require a proposition

`LeanAideCore/LeanAideCore/PaperCodes.lean` accepts a translated expression
when its inferred type is any `Sort`:

```lean
if univ.isSort then
  ...
  return type
```

The caller later asks `isProp type`; if the answer is false,
`theoremCodeCore` emits a `noncomputable def` instead of rejecting the theorem
translation. This is how Lemma 6 became:

```lean
noncomputable def lemma_6 :
    {Ω : Type u} → [MeasurableSpace Ω] → Measure Ω → (Ω → ℝ) → Prop := by
  ...
  exact True
```

The log shows that the LLM proposed a definition `IsRademacher` followed by an
expectation theorem. The sub-line recovery in the theorem-expression
elaborator retained only the predicate type of the definition. It was therefore
syntactically type-correct but unrelated to the Lemma 6 claim.

Required change: for every JSON object whose type is `"theorem"`, require
`isProp type = true` inside `translateToPropStrictAux` and reject all
type-valued or predicate-valued results. Sub-line recovery must also retain the
theorem command corresponding to the requested claim, not an arbitrary
elaborable definition or prefix from a multi-command answer. A non-`Prop`
result must never be silently changed into a `def` by a theorem handler.

#### 2. Definition renaming is computed and then discarded

In `LeanAideCore/LeanAideCore/PaperCodes.lean`, `defCode.defCmdStx` pattern
matches the translated definition and constructs a command using the JSON
`name`, but the reconstructed command is discarded. The code then executes:

```lean
let cmds := #[cmd]
`(commandSeq| $cmds*)
```

where `cmd` is the original LLM command. Consequently the JSON names
`PseudoLength`, `IsLength`, `IsHomogeneousPseudoLength`, `commutator`, and
`IsTorsionFreeAbelian` became LLM-selected names instead.

Required change: bind the result of the syntax match, for example
`let renamedCmd ← match cmd with ...`, and return `#[renamedCmd]`. Either the
rest of the generated statements must consistently use these canonical JSON
names, or explicit abbreviations should be emitted. Silent renaming makes later
translation prompts and source-level references unstable.

#### 3. Lemmas 5, 6, and 12 do not have formal local contexts

The remaining prose assumptions are not enough to create Lean binders:

- Lemma 5 mentions `f`, Rademacher variables, `S2n`, and expectation without a
  formal sample space or a finite expectation definition.
- Lemma 6 has the same problem and also needs the distribution/independence
  hypotheses that make the estimate true.
- Lemma 12 uses `VQ := A ⊗[ℤ] ℚ` and `normQ` in prose. Rejected candidates use
  these identifiers before binding them.

##### Lemma 5 had valid candidates that the checker never accepted

The weak source context is not the whole explanation for Lemma 5. The LLM
returned eight candidates, and several repaired the missing context by defining
`c`, `f`, the finite sign space, the random-walk sum, and uniform expectation
inside the statement. Exact candidates 3, 5, and 7 from the log compile
independently with only the expected `declaration uses sorry` warning. Candidate
3, for example, has the following proposition:

```lean
∀ {G : Type u} [Group G] {l : G → ℝ},
  IsHomogeneousPseudoLengthFunction l →
    ∀ (x y : G) (n : ℕ),
      let c : G := commutatorOf x y
      let f : ℤ → ℤ → ℝ := fun m k => l (x ^ m * c ^ k)
      let S2n : (Fin (2 * n) → Bool) → ℤ := fun ε =>
        ∑ i : Fin (2 * n), if ε i then (1 : ℤ) else (-1 : ℤ)
      f 0 (n : ℤ) ≤
        (Fintype.card (Fin (2 * n) → Bool) : ℝ)⁻¹ *
          ∑ ε : (Fin (2 * n) → Bool),
            f (S2n ε) (-(S2n ε) / (2 : ℤ))
```

This is the appropriate formal interpretation of the expectation: uniform
averaging over every sign assignment `Fin (2*n) → Bool`. Independence is built
into the product sample space, so no measure-theory objects are required merely
to state the lemma. The proof must later establish that `S2n ε` is even and
iterate Lemma 4, but these are proof obligations, not statement-elaboration
problems.

The valid statements were lost through the following checker sequence:

1. `TheoremElabCheck.elabThm4Aux` executes
   `s.replace "\n" " "` before parsing. The first candidates use Lean's
   layout-sensitive consecutive `let` syntax. Flattening their newlines removes
   the separators and makes otherwise valid declarations fail to parse.
2. `elabThm4` then invokes `lineBlocks`, which enumerates every nonempty subset
   of lines. Subsets can retain `f 0 ...` or `f S ...` while dropping the
   preceding `let f` and `let S`, producing the logged `Function expected at f`
   and unknown-`S` errors. Other subsets retain only a real-valued sum, so the
   target is not a proposition. These diagnostics describe corrupted recovery
   fragments, not the complete candidates returned by the model.
3. Recovery can also find a fragment containing only `sorry` or a target ending
   in `≤ sorry`. `elabThm4` returns that fragment as an elaborated expression.
   In `translateToPropStrictAux`, the `type.hasSorry` branch throws immediately
   instead of recording the bad candidate and continuing the `for out in
   output` loop. Consequently the later valid finite-sample candidates are
   never checked. The second registered theorem handler repeats the same failed
   process.

This failure occurs during top-level statement translation, before the dummy
theorem used for proof prompts is installed; dummy-prelude contamination is not
the cause here.

Required changes: preserve newlines and parse the complete extracted Lean
command; replace `lineBlocks` with bounded syntax-aware extraction of a fenced
declaration or theorem term; never accept a recovery fragment containing
`sorry`; and make an invalid/sorry/non-`Prop` candidate append a structured
diagnostic and `continue` to the next LLM output rather than aborting the whole
translation loop.

The log reports exactly two top-level source-processing failures, for Lemmas 5
and 12. Lemma 6 is more dangerous: it does not fail loudly, but translates to
the wrong declaration.

The source should still be supplied to codegen in already formal Lean shape.
For the probability section, the most robust choice is a finite sample space
`Fin (2*n) → Bool`, with explicit definitions for the sign, the sum, and the
uniform expectation. This avoids introducing measure theory merely to express
a finite average. If the measure-theoretic formulation is kept, bind a
probability measure, a finite family of measurable Rademacher variables,
pairwise independence, the definition of `S2n`, and integrability assumptions.

Lemma 12 should have an explicit target of the form:

```lean
∃ normQ : Seminorm ℚ (A ⊗[ℤ] ℚ),
  ∀ a : A, normQ (TensorProduct.tmul ℤ a (1 : ℚ)) = p a
```

with torsion-freeness and all homogeneous pseudo-length axioms present as Lean
hypotheses, not prose preludes.

#### 4. Diagnostic lookup commands remain in generated code

The three `#check "..."` commands near the top only typecheck string literals;
they do not check the declarations described by those strings. They print
lookup diagnostics during compilation and enter the command prelude used by
later translation.

Required change: record lookup results in logs or comments. Do not emit them as
commands and do not add them to `cmdPrelude`.

### Proof-generation failures

#### 1. Commands are committed even when elaboration reports errors

`LeanAideCore/LeanAideCore/TranslateM.lean:addCommands` calls
`runFrontendM ... true` for each command, discards the message log, writes the
commands, and appends them to `cmdPrelude` regardless of errors. This allowed
the universe-invalid Proposition 7 and the malformed Lemma 13 to be written and
used as subsequent context.

Required change: elaborate the complete command sequence in a saved state,
collect error-severity messages, and commit the environment, output file, and
prelude only if the whole sequence succeeds. On failure, restore the state and
record a structured codegen error. The final full declaration must be checked;
successful statement elaboration with `:= by sorry` does not validate the
generated proof.

#### 2. Fallback `sorry` and recursive proof generation lose the active goal

`findTacticsI` uses

```lean
repeat (sorry)
```

as the default whenever automation fails. This makes failed proof search look
like a successful tactic sequence. The emitted Lemma 9 proof demonstrates the
observable result:

```lean
let ⟨barL, assert_17274311165594130021⟩ :=
  assert_11951970955198732883
repeat (sorry)
have assert_13313675123275672338 : ... := by
  repeat (sorry)
```

The first `repeat (sorry)` closes the theorem goal. The following `have` is
therefore invalid, and Lean reports `No goals to be solved`. A minimal proof
containing `repeat (sorry)` followed by a `have` reproduces the same diagnostic.
The July 20 log records this diagnostic seven times, all while generating
Lemma 9.

The generator-side mechanism is more subtle than deliberately receiving an
empty goal list and ignoring it. Lemma 9 contains a nested JSON `proof` step,
followed by six more top-level proof steps. The sequence is:

1. The outer `getCodeTacticsAux` calls `getCode` for the nested `proof` using
   the current theorem metavariable.
2. The tactic branch of `proofCode` recursively calls `getCodeTactics` on that
   same metavariable under `withoutModifyingState`. However, the
   `MonadBacktrack` instance for `TranslateM` saves only `Translate.State`
   fields such as preludes and definitions. It does not save the enclosing
   `TermElabM`/`MetaM` state or metavariable context.
3. The nested generator executes its component tactics with
   `runForSingleGoal`. This partially assigns the original parent metavariable
   to a proof term containing a new unresolved child metavariable. It then
   appends the fallback `repeat (sorry)` to the returned syntax without running
   it or returning a terminal/failure status.
4. The outer generator attempts to replay the returned nested tactic block on
   the original parent metavariable. That metavariable is already assigned, so
   `Elab.runTactic` raises `No goals to be solved`. The first logged failure
   prints:

   ```text
   Tactics failed on ∃! barL, ... : No goals to be solved
   Assignment: true; have assert_10162204231442207603 := ...; ?m.2190
   ```

   The assignment is not a completed proof: the printed `?m.2190` is the real
   unresolved child goal.
5. `runForSingleGoal` catches the exception and returns the same assigned parent
   `mvarId` as if it were a valid remaining goal. `getCodeTacticsAux` consequently
   processes the six later JSON steps against that assigned metavariable,
   accounting for the other six `No goals to be solved` events.
6. At the end, `getCodeTactics` tests only `goal.isAssigned` and returns the
   accumulated syntax. An assigned metavariable whose value still contains an
   unassigned metavariable is incorrectly classified as complete. The returned
   syntax contains the nested terminal `repeat (sorry)` followed by the later
   top-level tactics, producing the malformed final proof.

Thus the earlier description was correct about the final Lean program but
imprecise about codegen's internal state: codegen did not knowingly receive
zero goals and continue. Recursive generation lost the real child goal,
continued with an assigned parent goal, and emitted syntax in which a terminal
tactic precedes later steps.

Required changes:

1. Make recursive tactic generation state-safe. Either require `getCode` tactic
   handlers to be pure with respect to `TermElabM`/`MetaM` state and replay their
   returned syntax exactly once, or return both syntax and the resulting active
   goals without replay. `withoutModifyingState` must not suggest that it saves
   metavariables when it saves only `Translate.State`; add an explicit helper
   that saves/restores both term-elaboration and meta state.
2. Change `runForSingleGoal` to return a structured success/failure result. On
   failure restore both saved states and never return an assigned metavariable
   as `some remainingGoal`.
3. Do not use `MVarId.isAssigned` as the definition of proof completion. Track
   the active goals returned by tactic execution, or recursively instantiate
   the assigned expression and reject it if it contains unassigned
   metavariables. The existing `Lean.Expr.hasUnassignedExprMVar` helper already
   performs the recursive boolean check. When the actual child goals are needed,
   use:

   ```lean
   def remainingGoals (goal : MVarId) : MetaM (List MVarId) := do
     let proof ← instantiateMVars (mkMVar goal)
     let deps ← getMVars proof
     deps.toList.filterM fun m => return !(← m.isAssigned)
   ```

   `instantiateMVars` recursively replaces every assigned metavariable by its
   assigned value. `getMVars` then collects the metavariables still present, and
   the final filter retains only genuinely unassigned goals. An empty list means
   recursively solved; one element is the next goal; multiple elements must be
   represented as multiple active goals rather than collapsed to one. For a
   boolean-only check, use
   `!(← (mkMVar goal).hasUnassignedExprMVar)`. Prefer the goal list returned
   directly by successful `Elab.runTactic` whenever it is available; the helper
   is the correct replacement when recovering from or auditing an assigned
   parent expression.
4. Represent proof-search failure as data (`none`/error), not as a closing
   tactic. Insert a single `sorry` only at the outermost declaration after
   generation has stopped for that goal, and never append tactics after it. A
   best-effort mode can emit one explicit hole, but must propagate a terminal
   status through nested proof generation.

#### 3. Failed proof steps are converted to `skip`

The log contains 169 `Error in getCode `tacticSeq` for source` events; 147 are
explicitly attached to `assert_statement` nodes. There are also 56 occasions
where structured steps finish with a goal still open, compared with only 17
top-level automation closures. In `getCodeTacticsAux`, an exception from a
proof step is caught and replaced by:

```lean
`(tacticSeq | skip)
```

This is the direct source of much of the 165-`skip` output. It loses the
location and reason for the failed obligation while allowing generation to
continue into a less coherent local context.

The 169 events are not 169 independent bad translations. Parsing the source
JSON attached to each event gives:

| source kind | events |
|---|---:|
| `assert_statement` | 147 |
| `construction_proof` | 10 |
| `assume_statement` | 8 |
| `theorem` | 4 |

There are only 53 distinct failing source objects. Before Lemma 13 there are 39
events; Lemma 13 and its recursively expanded construction account for the
remaining 130. For example, "B is the metric completion of W" is translated 20
times, while the rational scalar-extension and approximating-sequence claims
are each retried eight times. This repetition explains why four theorem-level
failures plus 165 emitted `skip`s correspond to 169 logged source failures.

##### The main candidate-rejection bug is an invalid dummy theorem prelude

Many candidates shown as rejected in the log are valid Lean when checked in a
clean version of the displayed local context. The failure is already present
in the text prepended to them. In
`LeanAideCore/LeanAideCore/PaperCodes.lean`, nested theorem proof generation
temporarily executes:

```lean
let dummyCmd ← `(command| theorem $nameIdent : $typeStx := by sorry)
Translate.addCommand dummyCmd
```

There is a good reason to expose the enclosing theorem signature to the model:
nested proof-step translations benefit from seeing the theorem name, complete
target, and surrounding mathematical context. `cmdPreludeBriefBlob?` turns the
command prelude into the "Code context" section of the LLM prompt, and the
comment in `PaperCodes.lean` confirms that this was the dummy's intended role.
That role is prompt metadata only. It does not justify installing the theorem in
the frontend checking context, where it both causes the failures below and can
make a circular reference to the theorem under construction appear valid.

The translated `type` has first passed through `dropLocalContext`, so it may be
an expression open in the current local free variables. The dummy is therefore
not necessarily a valid global command by itself. Moreover,
`TranslateM.withCommandPrelude` emits `cmdPreludeForFrontendBlob?` before
`variablePreludeForFrontendBlob?`, placing this open dummy before the command
that declares its variables.

The kernel-submodule failure in Lemma 13 is a concrete example. The frontend
input is ordered as follows:

```lean
theorem homogeneous_root_lemma_13_proof_root_kernel_subspace :
  ∃ (N : Submodule ℚ VQ),
    (↑N : Set VQ) = {v : VQ | normQ v = 0} := by sorry

variable {VQ : Type u} [AddCommGroup VQ] [Module ℚ VQ]
  (normQ : Seminorm ℚ VQ)

example : ∀ {VQ : Type u} [AddCommGroup VQ] [Module ℚ VQ]
  (normQ : Seminorm ℚ VQ),
  ∃ (N : Submodule ℚ VQ),
    (↑N : Set VQ) = {v : VQ | normQ v = 0} := by sorry
```

Lean reports `failed to synthesize ... AddCommMonoid VQ` in the first command,
where `VQ` is still an auto-implicit of unknown structure. The fully bound
`example` is not the source of that error and compiles independently. The same
thing occurs in Lemma 3: the dummy theorem for the claim about `l a` precedes
the declarations of `l` and `a`, producing `Function expected at l`; the
fully-bound candidate also compiles independently.

`elabThm4Aux` collects errors from the complete frontend input and associates
them with the candidate currently being tested. It does not distinguish a
prelude error from an error whose source range is in the candidate. Therefore
one invalid dummy theorem causes every LLM alternative, including good ones, to
be rejected.

Required changes:

1. Do not put the prompt-only dummy theorem into the frontend command prelude.
   If it must be a command, close its type over every local free variable (for
   example with `mkForallFVars`) before delaboration. Merely moving the variable
   prelude before it fixes these displayed cases, but closing or eliminating the
   dummy is safer for local lets and hypotheses.
2. Validate the prelude independently before checking candidates. A prelude
   error must be reported as a generator error, not attached to every candidate.
   Candidate acceptance should consider only errors whose source positions are
   in the candidate body, or elaborate the candidate directly in the current
   environment/local context.
3. Separate state-only, prompt-only, and elaborating APIs, and name them by
   their effects. In particular, the current `addCommand` only pushes syntax
   into `cmdPrelude`; it does not run or elaborate anything, so a name such as
   `addCommandToPrelude` is required. Use a separate `addPromptContext` (which
   need not contain a Lean command) for the enclosing theorem, and reserve names
   such as `runAndCommitCommand(s)` for operations that validate and update the
   environment. The current `addCommands`, which elaborates, writes, and then
   appends while discarding errors, should be split into explicit validation and
   transactional commit operations.

##### Exhaustive line recovery amplifies each false rejection exponentially

If the full candidate fails, `TheoremElabCheck.elabThm4` calls `lineBlocks`.
`lineBlocks` returns every nonempty subset of the input lines in their original
order: a candidate with `n` lines produces `2^n - 1` additional checks. The log
contains `Checking groups: 1023` and `Checking groups: 8191`, corresponding to
10- and 13-line answers. Since the invalid prelude makes every subset fail,
this recovery cannot succeed and only multiplies the same unrelated error.

Across the log there are 72,191 parsed elaboration events containing 214,318
command-error messages, although there are only 9,922 distinct candidate texts
and 53 distinct failed source objects. The most common raw messages are 104,644
typeclass failures and 66,574 `Function expected` errors. These numbers mostly
measure prelude contamination, recursive retries, and subset expansion, not the
number of distinct mathematical mistranslations.

Required change: replace `lineBlocks` with bounded, syntax-aware recovery. Try
the full response, extract one fenced Lean declaration/term, and perhaps try a
small fixed number of suffixes after explanatory prose. Put a strict cap on
candidate variants. Never run subset recovery until the prelude itself has
passed validation.

##### Genuine translation failures remain behind the prelude bug

Some candidates really are ill-scoped or mathematically underspecified:

- Local notation introduced only in prose is not available to Lean. A
  `let_statement` without a `value` merely calls `addPrelude` and emits no Lean
  `let`. Later candidates consequently use unknown `C`, `C0`, `z`, `a`, `c`,
  `u`, or `v`, producing `Function expected`, type mismatches, or unknown
  identifiers. Such notation must be represented by a typed local definition,
  or expanded before translation.
- The eight failing `assume_statement`s have JSON such as
  `{"variable_type":"G","variable_name":"x"}`, while `assumeCode` requires an
  `assumption` string. This is a schema/handler mismatch, not an LLM failure.
  Normalize these nodes upstream or teach the handler to create a typed local
  binder from `variable_name` and `variable_type`.
- The probability candidates use free `f` and `S`, and write informal finite
  sums without defining a sample space, sign variables, distribution, or
  expectation. The input needs an explicit finite probability model before a
  Lean proposition can be generated reliably.
- Several completion candidates use quotient coercions and real scalar
  structure before the needed instances and compatibility laws have been
  constructed. In particular, structure witnesses intended to become
  instances must be installed with `letI`, and simultaneous ℚ/ℝ actions require
  the appropriate scalar-tower compatibility. These are genuine formalization
  issues, but the current log cannot reliably classify individual candidates
  until prelude errors are separated from candidate errors.

Finally, retain the structured source error and stop generation for that
subgoal, or emit a named terminal hole with the original JSON id/claim in a
comment. `skip` is appropriate only for a genuinely side-effect-only JSON node,
not as recovery from a failed assertion or theorem translation. Cache-key
correctness cannot repair this problem: a correct cache will faithfully replay
the invalid-prelude result.

#### 4. Proposition 7 leaks an unused universe into the theorem value

The proof contains a local assertion over `{Ω : Type v}` while the theorem
statement mentions only universe `u`. The proof term therefore has level
parameters `[u,v]`, but the constant type expects only `[u]`.

Required change: reject proof terms whose universe parameters exceed those of
the declaration type. For this particular proof, remove the underspecified
probability assertions or bind their sample space at a universe already present
in the theorem. Full-command elaboration before commit would catch this
automatically.

#### 5. `constructionProofCode` delaborates an unresolved metavariable instead of its assigned value

In `LeanAide/PaperCodes.lean`, the construction handler does:

```lean
let existenceType ← translator.translateToPropStrict fullClaim
let existenceGoal ← mkFreshExprMVar existenceType
...
let existenceSyntax ← delabDetailed existenceGoal
```

`existenceGoal` is the metavariable expression. Delaborating it produces the
literal `?m.2643`/`?m.2645` syntax seen throughout Lemma 13. Delaborating the
original `existenceType` would avoid the literal metavariable, but it is not the
best recovery: that translated type may still contain metavariables that were
resolved while the proof tactics assigned `existenceGoal`.

The robust helper is `instantiateMVars`, which recursively substitutes assigned
metavariables with their assigned expressions. Recover the root assignment
explicitly, instantiate all metavariables in it, and infer its resolved type if
syntax is needed in the type position:

```lean
let goalId := existenceGoal.mvarId!
let some assigned ← getExprMVarAssignment? goalId
  | throwError "construction proof did not assign its existence goal"
let assigned ← instantiateMVars assigned
let assignedType ← instantiateMVars (← inferType assigned)
let existenceSyntax ← delabDetailed assignedType
```

Equivalently, `instantiateMVars existenceGoal` resolves the root metavariable
when it is assigned, but the explicit `getExprMVarAssignment?` form makes an
unassigned construction fail immediately. If the generated syntax is intended
for a value position, delaborate `assigned` itself; for the type after
`have h :`, delaborate `assignedType`. A successfully assigned proof term must
have a type definitionally equal to the original goal type, while inference
from the resolved value also incorporates metavariable assignments made during
proof generation.

The larger design problem is that the handler translates `full_claim`, creates
an independent goal, proves it, destructures it, and then translates and proves
`claim` again. For nested construction proofs this replays the same large proof
tree several times. The log and output show repeated completion, real-scalar,
and canonical-map blocks, explaining both the eight-hour run and the explosive
Lemma 13 body.

Required change: operate on the current goal and its actual existential binder.
Translate the witness once, apply `refine ⟨witness, ?_⟩` (or the corresponding
multi-witness sequence), and run only the verification needed for the resulting
goal. Do not independently retranslate `full_claim`, and do not generate a
second proof of the same verification proposition.

#### 6. Lemma 13 contains false or missing-hypothesis obligations

Even after repairing the syntax, the generated proof is not mathematically
usable. Representative obligations assert:

```lean
∀ (r : ℝ), Tendsto (fun n => (q n : ℝ)) atTop (nhds r)
∀ (q : ℕ → ℚ) (w : ℕ → B), ∃ b, Tendsto (fun n => (q n : ℝ) • w n) atTop (nhds b)
∀ {L L' : B}, L = L'
q • w = (q : ℝ) • w
```

for arbitrary sequences, arbitrary normed spaces, or unrelated scalar actions.
These are false without convergence, Cauchy, completeness, approximation, and
scalar-tower hypotheses. Some generated fragments derive `0 = 1` from these
false premises and then close later goals by contradiction. The proof also
defines `completionB` using `Classical.choose (lemma_13 normQ)`, a circular use
of the theorem being defined, and later says `use iota` where no such local
identifier has been constructed.

Lemma 13 should not be synthesized from the current prose construction. Add a
hand-proved reusable Lean theorem for the Banach envelope of a seminormed
`ℚ`-space, then make codegen apply that theorem. Mathlib already supplies the
same-field completion facts such as `UniformSpace.Completion.toComplₗᵢ`; the
nontrivial missing part is extending the rational scalar action continuously to
`ℝ`. That extension needs one coherent library construction, not dozens of
generated local claims.

#### 7. Duplicate theorem handlers repeat expensive failing work

Both `LeanAideCore/LeanAideCore/PaperCodes.lean` and
`LeanAide/PaperCodes.lean` register a `"theorem"` codegen handler. The log
repeatedly reports `found 2 functions for key theorem`; `getCode` tries them
sequentially, so a hard statement-translation failure such as Lemma 5 or Lemma
12 is performed twice. The two implementations have also diverged, which makes
the fallback result depend on registration order.

Required change: keep one authoritative theorem handler, or make the second a
small, explicitly different fallback that consumes the first handler's
structured failure without re-running the same LLM translation and frontend
search.

### Comparison with `CodeGen/homogeneous.lean`

The earlier file fails independently with invalid theorem fallbacks for
Definitions 2 and 3, a universe error in Lemma 4, and malformed Lemma 13 syntax.
Its active generated portion contains 96 `sorry` occurrences and 31 `skip`
tactics. It also emits two `#eval "command skipped..."` placeholders.

The July 20 file is better at the statement/definition layer but worse in proof
size and still not compilable:

| Area | Earlier file | July 20 live file |
|---|---|---|
| Definition 2/3 | Invalid theorems whose declared types end in `→ Prop` | Correct predicate definitions |
| Definition 4 | No usable generated commutator definition | Correct `commutatorOf` definition |
| Lemmas 1--4 | Missing essential hypotheses; several statements are false | Essential group/length hypotheses and definitions are present |
| Lemmas 5--6 | Statements emitted, but omit the distribution assumptions needed to be true | Lemma 5 omitted; Lemma 6 silently replaced by a vacuous predicate-valued definition |
| Proposition 7 / Lemma 8 | Missing homogeneity hypotheses | Statements corrected; proofs still fail |
| Lemma 9 | Only unique factorization, without preservation of the length axioms | Stronger and faithful statement; nested proof generation assigns the parent mvar, loses its child goal, and emits a terminal `repeat sorry` before later tactics |
| Lemma 10 | Missing all axioms on `p` | Correct hypotheses; one remaining proof hole |
| Lemmas 11--12 | Both absent/skipped | Lemma 11 emitted; Lemma 12 still omitted |
| Lemma 13 | Malformed, 67 `sorry` occurrences within its declaration | Still malformed and expanded to 79 `sorry` occurrences plus 130 `skip`s |
| Theorem 14 / Corollary 15 | Not emitted | Still not emitted in the partial live file |

In short: the cache/context repair fixed the original definition cascade and
the new translator produces much better theorem statements. The current
bottleneck is no longer the first predicate definition. It is the lack of a
strict proposition boundary, unchecked command commits, `sorry` being used as
control flow, recursive proof generation confusing assigned parent mvars with
completed goals, and the construction-proof handler generating metavariables
and duplicating proof trees.

### Recommended implementation order

1. Remove or close the open dummy theorem used during nested proof generation,
   validate frontend preludes separately, and never attribute a prelude error
   to the candidate being checked.
2. Preserve Lean layout while parsing candidate declarations, and replace
   exponential `lineBlocks` recovery with a small bounded, syntax-aware set of
   candidate extractions that cannot promote `sorry` or proof-body fragments.
3. Make `translateToPropStrict` genuinely `Prop`-strict for theorem JSON and
   reject Lemma 6-style predicate/type results. Record candidate-local
   `sorry`/mvar/non-`Prop` failures and continue checking later LLM outputs.
4. Fix `constructionProofCode` by recursively instantiating the existence
   goal's assigned value, inferring its resolved type when needed, and,
   preferably, operating directly on the current existential goal without
   replaying `full_claim` and `verification`.
5. Make `addCommands` transactional: no environment update, prelude append, or
   file write unless the complete generated command elaborates without errors.
6. Isolate `TermElabM`/`MetaM` state during recursive tactic generation, make
   `runForSingleGoal` return structured failure instead of an assigned mvar, and
   track actual remaining child goals rather than testing only `isAssigned`.
7. Replace `repeat (sorry)` as an internal success value with an explicit proof
   failure result; emit at most one terminal hole in best-effort output.
8. Stop converting failed assertion/theorem steps into `skip`, materialize
   typed locals instead of prose-only `let_statement`s, accept the structured
   `assume_statement` schema, and consolidate the duplicate theorem handlers.
9. Preserve JSON definition names by returning the reconstructed command from
   `defCode`.
10. Replace lookup `#check` commands with log entries/comments.
11. Preformalize the finite-probability Lemmas 5--6 and tensor Lemma 12, and add a
   hand-written reusable Banach-envelope theorem for Lemma 13.

The existing implementation sites for these changes are now marked with
`TODO(generation-check-homogeneous)` comments. The markers cover:

| concern | marked Lean files |
|---|---|
| prompt-only dummy, prelude roles, API naming and transactional commits | `TranslateM.lean`, `Translator.lean`, `Translate.lean`, `PaperCodes.lean` |
| prelude/candidate error separation and bounded recovery | `TheoremElabCheck.lean`, `Aides/Basic.lean`, `Translate.lean` |
| strict propositions and theorem-handler consolidation | both `PaperCodes.lean` implementations |
| assigned construction metavariables and duplicated construction proofs | `LeanAide/PaperCodes.lean` |
| recursive tactic-state isolation, failed replay and real remaining-goal tracking | `CodegenCore.lean`, `RunTactics.lean`, `TranslateM.lean`, `LeanAideCore/PaperCodes.lean` |
| `skip`, `repeat sorry`, proof status and command accumulation | `CodegenCore.lean`, both `PaperCodes.lean` implementations, `TranslateM.lean` |
| typed local notation and assumption-schema alignment | `DocumentSchema.lean`, both local-statement handlers |
| definition renaming/fallback and diagnostic `#check` output | `LeanAideCore/PaperCodes.lean`, `LeanAide/Codegen.lean` |

The probability/tensor formalizations and reusable Banach-envelope result also
require new domain declarations and upstream structured data, so they have no
single existing implementation body to mark. Their current entry boundaries
are marked at the document schema/local-definition handlers and at
`constructionProofCode`.

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

   The preferred robust fix is the environment-relative option: add an optional
   cache salt/environment-hash parameter to `runFrontEndForMessages` and
   `checkElabFrontM` in `LeanAideCore/LeanAideCore/SimpleFrontend.lean`. The
   current cache path is based only on `input.hash` and `leanToolchain`, so it is
   unsound whenever the same input string is elaborated in different generated
   environments. In the `TranslateM` checks, the salt can be the hash of the
   full unfiltered generated context, for example `cmdPreludeBlob.hash`, or a
   hash of the relevant `TranslateM` state if generated declarations can enter
   the environment outside `cmdPrelude`.

   Suggested shape:

   ```lean
   def runFrontEndForMessages
       (input : String) (envHash? : Option UInt64 := none) : MetaM MessageLog := do
     let salt := envHash?.map toString |>.getD "noenv"
     let cacheFile := (← cachePath) / "frontend" /
       s!"{input.hash}_{salt}_{← leanToolchain}.json"
     ...

   def checkElabFrontM
       (s : String) (envHash? : Option UInt64 := none) : MetaM (List String) := do
     let log ← runFrontEndForMessages s envHash?
     ...
   ```

   Then `translateDefCmdM?` and the theorem elaboration checks should pass this
   salt whenever they call `checkElabFrontM (← withCommandPrelude ...)`. With
   this change, `commandNeededForFrontendPrelude` can continue serving as a
   duplicate-declaration guard, but cached frontend results will no longer be
   reused across incompatible generated environments.

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

## July 20 Generic Claim-Closure Fix and Live Rerun

The recommendation to put `f`, the finite sign space, the random-walk sum, and
the finite expectation in the formal claim is a change to the generated JSON,
not a Lemma-5-specific Lean workaround. It is now implemented generically in
the Python claim-audit stage.

### Generic Python changes

`mathdoc_agent/orchestration/claim_audit.py` now supplies each claim audit with:

- a scope classification (`theorem_statement`, local theorem claim, or
  standalone claim);
- the enclosing theorem's source text and structured hypotheses;
- compact summaries of named declarations available in the document;
- mandatory `closure_risks` when a theorem uses a structured local definition
  that is not represented by a Lean `let`, or uses unresolved probability
  language; and
- bounded batches controlled by `MATHDOC_AGENT_CLAIM_AUDIT_BATCH_SIZE`
  (default `30`).

The rule is independent of identifier names and subject matter. Any theorem
marked `requires_closed_lean_repair` must be replaced by a complete Lean
proposition term which binds all variables and reproduces structured local
definitions with their existing names. Fully specified finite uniform
experiments are represented by a finite product sample space and a normalized
finite sum. Experiments which are not finite and fully specified must instead
bind the full probability context.

The auditor also now treats bundled Lean objects as types. Thus a requested
seminorm is represented as `normQ : Seminorm ℚ VQ`, using its coercion to a
function, rather than the invalid shape `normQ : VQ → ℝ` followed by
`Seminorm ℚ VQ normQ`. The same rule applies generically to morphisms, linear
maps, measures, and other bundled structures.

Two interactions found by the live rerun were fixed:

1. The later informal-notation pass used to replace every `:=` by prose
   `is defined as`, corrupting valid Lean `let` binders produced by the claim
   auditor. It now preserves `:=` in syntactically valid Lean `let` bindings
   while continuing to repair assignment-shaped prose.
2. The final linter used to put `lean_validation` beside `document` at the JSON
   root. That makes the root object undispatchable by CodegenCore. Global lint
   metadata is now nested inside the document object, and duplicate lint issues
   are removed.

### Real API rerun

The complete Python pipeline was rerun with the real OpenAI agents. The API key
was inherited from the `OPENAI_API_KEY` environment variable; no fake agent or
fabricated response was used:

```bash
./venv/bin/python -m mathdoc_agent.pipeline \
  results/homogeneous.md \
  --id homogeneous \
  -o results/homogeneous.json
```

One calculation-refinement call and the document-wide dependency rewrite hit
the configured ten-minute bound; each succeeded on the automatic retry. The
claim audit then completed in seventeen bounded batches. After discovering the
`:=` interaction, the regenerated JSON was passed through the corrected live
claim audit and notation repair once more. The final JSON has a single root key,
`document`, and no `let ... is defined as` corruption.

The similarity server was unavailable during the initial definition-reuse
stage but was restarted and queried directly afterward. It found no exact
Mathlib definition for the homogeneous pseudo-length predicate. For
torsion-freeness it returned related `IsAddTorsionFree` theorems and
`AddCommGroup.torsion`, but no exact replacement matching the generated
definition, so the conservative choice is to retain both generated definitions.

### Result for Lemma 5

The final claim at `/document/body/18/claim` is now closed with respect to its
local notation:

```lean
∀ (G : Type*) [Group G] (l : G → ℝ),
  IsHomogeneousPseudoLength G l →
  ∀ (x y : G) (n : ℕ),
    let c : G := x * y * x⁻¹ * y⁻¹
    let f : ℤ → ℤ → ℝ := fun m k => l (x ^ m * c ^ k)
    let Omega : Type := Fin (2 * n) → Bool
    let eps : Omega → Fin (2 * n) → ℤ :=
      fun omega i => if omega i then 1 else -1
    let S2n : Omega → ℤ :=
      fun omega => Finset.univ.sum (fun i => eps omega i)
    f 0 n ≤ (Fintype.card Omega : ℝ)⁻¹ *
      Finset.univ.sum
        (fun omega : Omega => f (S2n omega) (-(S2n omega) / 2))
```

This is the requested change: `f`, the finite sample space, the sign variables,
`S2n`, and expectation are part of the proposition itself. Independence and
the uniform sign distribution are represented by ranging over all functions
`Fin (2*n) → Bool` with uniform weight, rather than by free measure-theory
objects or prose hypotheses.

Lemma 12 was repaired by the same mechanism. Its claim now contains

```lean
let VQ : Type* := TensorProduct ℤ A ℚ
∃ normQ : Seminorm ℚ VQ,
  ∀ a : A, normQ (TensorProduct.tmul ℤ a (1 : ℚ)) = p a
```

### Remaining boundary

Claim closure is fixed at the JSON level, but exact reuse of generated
definition signatures remains a separate boundary. The claims currently use
the canonical JSON names `IsHomogeneousPseudoLength` and
`IsTorsionFreeAbelianGroup`; the older Lean run generated different names such
as `IsHomogeneousPseudoLengthFunction`. The previously recommended Lean-side
name-preservation fix is therefore still required. In addition, the additive
use of homogeneous pseudo-lengths must be made type-compatible with the
multiplicative group definition, either by a distinct additive predicate or by
an explicitly stated conversion. These are signature/representation issues,
not free-local-notation failures.

Per the subsequent instruction, no further codegen run was performed. Final
verification for this change consists of the live Python-agent rerun, direct
inspection of the emitted closed claims, the restarted similarity-server
queries, and the Python regression suite.
