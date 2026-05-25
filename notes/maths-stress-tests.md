# Mathematics stress tests

A good way to test a proof is not only to ask “does the argument prove the theorem?” but also to ask:

> Does the argument fail exactly where it should fail?

This is especially useful for informal proofs, Lean formalizations, and agentic proof decomposition.

## 1. Hypothesis-weakening stress tests

Take a theorem

```text
H₁, H₂, ..., Hₙ ⊢ Conclusion
```

and systematically weaken or delete hypotheses.

For each weakened version, ask:

1. Is the weakened theorem false?
2. Can we produce a counterexample?
3. Does the proof actually use the removed hypothesis?
4. Does the proof break at the correct step?

Example:

```text
Every continuous function on a compact space attains its maximum.
```

Stress test:

```text
Every continuous function on a non-compact space attains its maximum.
```

Counterexample:

```text
f(x) = x on (0, 1).
```

A correct proof should use compactness, usually through open covers, sequential compactness, or existence of convergent subsequences. If the proof still goes through after deleting compactness, it is suspicious.

This test detects “ghost hypotheses”: assumptions present in the statement but not actually used, and missing hypotheses: assumptions needed in the proof but absent from the statement.

## 2. Hypothesis-strengthening sanity tests

Strengthen hypotheses and check whether the proof simplifies.

Example:

```text
Every continuous function on a compact Hausdorff space is bounded.
```

Strengthen to:

```text
Every continuous function on a finite discrete space is bounded.
```

The proof should become trivial. If it does not, the proof may be using unnecessarily heavy machinery or may not reflect the real structure of the result.

This is useful for discovering whether the proof is conceptually aligned with the theorem.

## 3. Conclusion-strengthening stress tests

Make the conclusion stronger, preferably falsely stronger.

Example:

```text
A continuous function on a compact space is bounded.
```

False strengthening:

```text
A continuous function on a compact space is constant.
```

A correct proof of boundedness should break before proving constancy. If the same proof template appears to prove the stronger claim, it is using an invalid inference.

This is especially useful for detecting overpowered lemmas, invalid generalization, or hidden uses of “obvious” statements.

## 4. Conclusion-weakening sanity tests

Weaken the conclusion and see whether the proof naturally factors through it.

Example:

```text
A differentiable function is continuous.
```

Weakened conclusion:

```text
A differentiable function is sequentially continuous.
```

The proof should either imply the weaker conclusion directly, or the theorem should be decomposable through an intermediate lemma.

This helps identify proof structure:

```text
differentiable
  ⇒ locally approximable by a linear map
  ⇒ continuous
  ⇒ sequentially continuous
```

For formalization, these weaker conclusions often become reusable lemmas.

## 5. Boundary-case tests

Test the theorem and proof on edge cases.

Examples:

```text
n = 0
n = 1
empty set
singleton set
zero module
zero ring
trivial group
identity map
empty product
degenerate interval [a, a]
```

A proof by induction should be checked especially at `0` and `1`.

A theorem about manifolds should be tested on:

```text
0-dimensional manifolds
manifolds with boundary
disconnected manifolds
non-orientable manifolds
```

A theorem about groups should be tested on:

```text
trivial group
finite cyclic group
free group
abelian group
non-abelian group
torsion group
```

Boundary cases often reveal implicit nonemptiness, positivity, regularity, or nondegeneracy assumptions.

## 6. Degeneration tests

Take a generic situation and let it degenerate.

Examples:

```text
distinct roots → repeated roots
transverse intersection → non-transverse intersection
full-rank matrix → rank-deficient matrix
smooth point → singular point
free group action → action with stabilizers
invertible operator → non-invertible operator
strict inequality → equality case
```

A common proof error is that the argument works only on an open dense set but the theorem is stated everywhere.

For example:

```text
If a polynomial has n distinct roots, then ...
```

The stress test is:

```text
What happens when two roots collide?
```

A correct proof should either handle the degenerate case separately or explicitly assume distinctness.

## 7. Uniformity tests

Look for places where the proof proves something pointwise but uses it uniformly.

Typical pattern:

```text
For every x, choose εₓ > 0.
Therefore choose ε > 0 working for all x.
```

Stress test:

```text
Can εₓ go to 0?
```

Example:

```text
Pointwise convergence fₙ(x) → f(x)
```

False strengthening:

```text
Uniform convergence fₙ → f
```

A proof using pointwise convergence should break if asked to prove uniform convergence. If it does not, it probably made an invalid quantifier move.

This is one of the most valuable proof stress tests.

## 8. Parameter-dependence tests

Track every chosen object and ask what it depends on.

For each choice:

```text
Choose N
Choose δ
Choose a subsequence
Choose a basis
Choose a representative
Choose a lift
Choose a chart
Choose a constant C
```

ask:

```text
Does it depend on x?
Does it depend on n?
Does it depend on ε?
Does it depend on the chosen representative?
Does it need to be uniform over a family?
```

A useful notation is to annotate choices explicitly:

```text
δ = δ(x, ε)
N = N(x, ε)
C = C(K)
subsequence = subsequence depending on y
```

Then test whether the later proof treats it as if it had fewer dependencies.

## 9. Choice-independence tests

Whenever the proof chooses representatives, charts, bases, lifts, splittings, or coordinates, test whether the output changes.

Example:

```text
Define F([x]) = [f(x)].
```

Stress test:

```text
If x ~ x', do we have f(x) ~ f(x')?
```

For a quotient construction, the proof must include a well-definedness check.

Similarly:

```text
Choose a basis of V and define a matrix.
```

Stress test:

```text
Does changing the basis conjugate the matrix?
Is the desired property invariant under conjugation?
```

This test detects non-canonical constructions being treated as canonical.

## 10. Local-to-global tests

If the proof proves something locally, test whether the local data glue.

Examples:

```text
local sections → global section?
local trivializations → global trivialization?
locally exact → globally exact?
local potentials → global potential?
local coordinates → global construction?
```

Stress test:

```text
What happens on overlaps?
Is there monodromy?
Is there a cocycle obstruction?
Does the construction depend on the path?
```

A classical failure pattern is:

```text
Every point has a neighborhood on which an object exists.
Therefore the object exists globally.
```

This is false unless there is a gluing argument.

## 11. Limit-passage tests

Whenever the proof says “pass to the limit,” ask what topology is being used and what properties are closed under that topology.

Stress questions:

```text
Is convergence strong enough?
Are the estimates uniform?
Does the limiting object remain in the same class?
Does the operation commute with the limit?
Is the property closed, open, or neither?
```

Example:

```text
Approximate by smooth functions and pass to the limit.
```

Stress tests:

```text
Do derivatives converge?
Does positivity survive?
Does invertibility survive?
Does injectivity survive?
Does the PDE still hold weakly or strongly?
```

Many properties are not preserved under weak limits.

## 12. Compactness tests

Compactness arguments deserve special testing.

Typical proof phrase:

```text
By compactness, extract a convergent subsequence.
```

Stress questions:

```text
What space is compact?
Which topology?
Is the sequence actually inside that compact set?
Does the limit lie in the intended space?
Is the compactness sequential or open-cover compactness?
Is the space first-countable/metrizable?
```

Stress weakening:

```text
Replace compact by bounded.
Replace compact by closed.
Replace compact by locally compact.
Replace finite-dimensional by infinite-dimensional.
```

If the argument survives these replacements unchanged, something is probably wrong.

## 13. Exactness and diagram tests

For homological algebra or category theory, stress-test every diagram.

Questions:

```text
Does every square commute?
Are arrows covariant or contravariant?
Is this a pullback or a pushout?
Is exactness used at the correct object?
Is the connecting morphism signed correctly?
Is naturality actually available?
```

False variant:

```text
Reverse one arrow.
Replace kernel by cokernel.
Replace pullback by pushout.
Remove exactness at one term.
```

A robust proof should fail in a specific place.

## 14. Functoriality and naturality tests

If the proof constructs something “naturally,” test it under morphisms.

Given a construction:

```text
X ↦ F(X)
```

ask whether for a map

```text
g : X → Y
```

there is a compatible map

```text
F(g) : F(X) → F(Y)
```

and whether diagrams commute.

Stress test:

```text
Does the construction commute with isomorphisms?
With restrictions?
With base change?
With pullbacks?
With composition?
With identity morphisms?
```

This often exposes hidden choices.

## 15. Invariance tests

If the theorem is invariant under some transformation, the proof should respect that invariance.

Examples:

```text
change of coordinates
change of basis
isometry
homeomorphism
group conjugation
field automorphism
equivalence of categories
renaming bound variables
```

Stress test:

```text
Apply the same theorem after an isomorphism. Does the proof produce the transported object?
```

If not, the proof may depend on accidental coordinates.

## 16. Model/countermodel tests

Try to instantiate the theorem in small explicit models.

For algebra:

```text
Z
Z/nZ
finite fields
matrix rings
dual numbers k[ε]/(ε²)
polynomial rings
free groups
cyclic groups
S₃
```

For topology:

```text
empty space
point
S¹
interval
Cantor set
indiscrete topology
Sierpiński space
non-Hausdorff line
```

For analysis:

```text
R
(0, 1)
ℓ²
L¹
C[0,1]
weak topology examples
```

For category theory:

```text
Set
Grp
Vect
Poset categories
one-object categories
empty category
```

Small models are excellent stress tests because false general statements often fail there.

## 17. Lemma-level counterexample tests

For each lemma, try to construct a counterexample to the lemma exactly as it is
stated, before looking at how it is used later.

Stress questions:

```text
Is the lemma false without an unstated hypothesis?
Can a small model violate the conclusion?
Can a boundary case violate it?
Can a degenerate object violate it?
Can the intended construction fail to cover all cases?
Does the proof actually prove this statement, or a nearby corrected version?
```

This should be done locally, lemma by lemma, not only for the final theorem.
Many paper-level errors enter through auxiliary lemmas whose statements are
slightly too broad, too uniform, or too canonical.

Useful workflow:

```text
Lemma L as stated
  ↓
Try smallest examples
  ↓
Try degenerate examples
  ↓
Try dropping implicit regularity/nonzero/nonempty assumptions
  ↓
If a counterexample appears, repair the lemma statement before using it
```

A correct proof should make counterexample search fail for a clear reason: the
hypotheses should block the attempted examples at a specific point.

## 18. Analogy-breaking tests

If the proof is adapted from a familiar setting, test the exact property that made the familiar proof work.

Examples:

```text
finite-dimensional → infinite-dimensional
commutative → noncommutative
field → ring
abelian group → nonabelian group
set → category
smooth → continuous
compact → locally compact
Hilbert → Banach
discrete group → locally compact group
```

Ask:

```text
Which step used the special property?
Does the replacement category still have it?
```

For example, in finite dimensions:

```text
closed and bounded ⇒ compact
```

fails in infinite-dimensional normed spaces.

So any proof using compactness from boundedness should fail under that stress test.

## 19. “Same proof proves too much” test

This is one of the most powerful meta-tests.

Take the proof and ask:

```text
What is the strongest statement this proof actually proves?
```

If the proof seems to prove a known-false theorem, locate the invalid step.

Example:

```text
The proof of convergence uses only pointwise boundedness.
```

But the conclusion needs compactness or equicontinuity.

Then the same proof might appear to prove a false Arzelà–Ascoli variant. That identifies the missing hypothesis.

This test is especially useful for proof assistants and LLM-generated proofs: if the proof template is too generic, it may be unsound.

## 20. Reverse-direction tests

For equivalences:

```text
A ⇔ B
```

test the two directions separately.

Stress questions:

```text
Does A ⇒ B really use A?
Does B ⇒ A use a different argument?
Is one direction only true under extra hypotheses?
```

False variant:

```text
A ⇒ B is true, but B ⇒ A is false.
```

Many erroneous proofs of equivalences prove only one direction, or prove both directions using an implicit symmetry that does not exist.

## 21. Induction-strength tests

For induction proofs, stress-test the induction hypothesis.

Questions:

```text
Is the induction hypothesis strong enough?
Is it too strong?
Is the recursive call on a genuinely smaller object?
Is the measure well-founded?
Are all constructors/cases covered?
Does the induction variable actually decrease?
```

False variant:

```text
Try to run the same induction using ordinary induction where strong induction is needed.
```

A correct proof should fail if the induction hypothesis is weakened below what is needed.

For nested induction:

```text
outer induction on n
inner induction on m
```

check that dependencies are not reversed.

## 22. Case-coverage tests

For case splits, check that the cases are:

```text
exhaustive
mutually appropriate
non-overlapping if needed
compatible with assumptions
```

Stress test:

```text
Can there be a third case?
What about equality?
What about zero?
What about singular cases?
What about impossible-looking cases?
```

A common error is:

```text
If a > 0, do X. If a < 0, do Y.
```

forgetting:

```text
a = 0.
```

In formal systems, this becomes constructor coverage or pattern coverage.

## 23. Dependency-graph tests

Build a dependency graph of results:

```text
Definition D
Lemma A
Lemma B
Proposition C
Theorem T
```

with arrows:

```text
X → Y means Y uses X
```

Stress tests:

```text
Is there a cycle?
Does a lemma use a later theorem?
Does a definition depend on a result that itself depends on the definition?
Does a proof use a corollary of itself?
```

This detects circularity.

For large mathematical documents, this test is very important.

## 24. Notation-expansion tests

Expand all suppressed notation.

Examples:

```text
identify A with B
up to canonical isomorphism
by abuse of notation
let C be a constant
after passing to a subsequence
the induced map
the natural map
```

Stress test:

```text
Write the actual map.
Write the actual dependency of C.
Write the actual subsequence extraction.
Write the actual canonical isomorphism.
```

If the proof becomes invalid when notation is expanded, the original proof hid a real gap.

## 25. Type-checking tests

Even for informal mathematics, ask what the types are.

Examples:

```text
Is this element in X or in a quotient of X?
Is this map defined on A or on its completion?
Is this equality in the object, or only after applying a functor?
Is this a function, a section, a germ, or an equivalence class?
Is this norm on V or on V*?
```

A large fraction of proof errors are type errors in disguise.

This is where Lean-style thinking is extremely valuable.

## 26. Definition-equivalence tests

When a proof uses a definition, check that it is the same definition throughout,
or that the claimed equivalent definitions are actually equivalent under the
current hypotheses.

Stress questions:

```text
Which definition of this term is being used here?
Does the cited theorem use the same definition?
Are the two definitions equivalent without extra assumptions?
Is the equivalence natural, or does it depend on choices?
Does the equivalence preserve all extra structure in the theorem?
```

Common examples:

```text
compactness by open covers versus sequential compactness
regularity in topology versus regularity in algebra
bundled versus unbundled structures
pointwise versus categorical definitions of a universal property
analytic versus algebraic definitions of the same object
```

If the proof switches definitions, insert the equivalence theorem as an explicit
lemma and stress-test its hypotheses.

## 27. Computational perturbation tests

For formula-heavy arguments, perturb the input and check consistency.

Examples:

```text
replace x by 0
replace matrix by identity
replace group element by identity
replace f by constant function
replace parameter t by 1
take the linear approximation
take a diagonal matrix
take a nilpotent matrix
```

If a complicated formula does not reduce to the expected simple formula, there is likely a sign, normalization, or convention error.

## 28. Alternative-proof comparison

Try to prove the same result by a different route.

Stress questions:

```text
Do both proofs use the same hypotheses?
Do they give the same constants?
Do they produce the same object?
Does one proof require stronger assumptions?
```

If proof A uses compactness and proof B does not, then either proof B is stronger, or proof B is missing a compactness-dependent step.

## 29. Formalization stress tests

For Lean or another proof assistant, useful stress tests include:

```text
Remove a hypothesis and confirm the proof no longer elaborates.
Generalize a typeclass assumption and see where it fails.
Replace equality by equivalence and locate needed transport.
Make all implicit arguments explicit.
Replace nonempty types by possibly empty types.
Turn off automation and see what exact lemmas are needed.
```

A particularly useful technique is to deliberately state false nearby lemmas and ensure the proof script cannot be adapted to prove them.

For example:

```lean
-- true
theorem continuous_on_compact_bounded ...

-- false stress version
theorem continuous_on_closed_bounded_in_infinite_dimensional_space_bounded ...
```

A proof framework should fail at the compactness extraction step, not later mysteriously.

## 30. LLM/agent proof stress tests

For LLM-generated proof sketches, use adversarial theorem variants.

Given a theorem, generate mutations:

```text
remove one hypothesis
reverse an implication
replace ∀ by ∃
replace compact by closed
replace finite by infinite
replace injective by surjective
replace equality by inequality
replace strict by non-strict
replace commutative by noncommutative
replace global by local
```

Then ask the proof agent:

```text
Does the original proof still apply?
Where does it fail?
Can you produce a counterexample?
Which hypothesis is used at which step?
```

This is an excellent guard against plausible but invalid proof sketches.

A useful workflow is:

```text
Theorem
  ↓
Proof sketch
  ↓
Dependency extraction
  ↓
Mutation of theorem
  ↓
Counterexample search
  ↓
Proof-break localization
  ↓
Revision of proof or statement
```

## 31. Proof-obligation extraction

Every nontrivial step should generate obligations.

Example proof step:

```text
Define F([x]) = [f(x)].
```

Obligations:

```text
1. If x ~ y, then f(x) ~ f(y).
2. F has the claimed domain and codomain.
3. F preserves the required structure.
```

Another example:

```text
Pass to a convergent subsequence.
```

Obligations:

```text
1. The sequence lies in a compact space.
2. The compactness notion gives subsequences.
3. The limit lies in the desired set.
4. The relevant property passes to the limit.
```

Stress testing then asks whether each obligation is still provable under theorem mutations.

## 32. Counterexample-guided proof testing

For each hypothesis, try to find a minimal counterexample when it is removed.

Template:

```text
Theorem: H₁ ∧ H₂ ∧ H₃ ⇒ C

Remove H₁:
  Find example satisfying H₂, H₃, not C.

Remove H₂:
  Find example satisfying H₁, H₃, not C.

Remove H₃:
  Find example satisfying H₁, H₂, not C.
```

Then map counterexamples to proof steps:

```text
H₁ is used in Step 2.
H₂ is used in Step 5.
H₃ is used in Step 7.
```

This gives a good audit trail:

| Hypothesis    | Needed? | Counterexample if removed         | Proof step using it    |
| ------------- | ------: | --------------------------------- | ---------------------- |
| compactness   |     yes | `f(x)=x` on `(0,1)`               | subsequence extraction |
| continuity    |     yes | unbounded function on compact set | image compactness      |
| Hausdorffness |   maybe | depends on theorem                | uniqueness of limits   |

This is valuable both for human proof review and automated proof checking.

---

## A compact stress-test checklist

For a proof, ask:

```text
1. Remove each hypothesis. Does the theorem become false? Does the proof break?
2. Strengthen the conclusion. Does the proof incorrectly prove too much?
3. Check boundary cases: empty, zero, one-dimensional, singular, equality case.
4. Track all dependencies of choices.
5. Check all quotient/representative constructions for well-definedness.
6. Check all local-to-global steps for gluing.
7. Check all limit steps for topology, uniformity, and closedness.
8. Check all compactness steps for the exact compact space used.
9. Expand suppressed notation and canonical identifications.
10. Build the dependency graph and look for circularity.
11. Test small explicit models and degenerate examples.
12. Try to construct counterexamples to each lemma exactly as stated.
13. Check that all equivalent definitions are equivalent under the hypotheses.
14. For equivalences, test both directions independently.
15. For induction, check base cases, decrease, and hypothesis strength.
16. For formalization, remove hypotheses and make implicit data explicit.
```

The guiding principle is:

> A robust proof should not merely prove the theorem; it should fail predictably on nearby false statements.

That is often the fastest way to locate the real mathematical content of the proof.
