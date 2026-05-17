# Research Mathematics Errors

## 1. Missing or weakened hypotheses

A theorem is stated under assumptions that are insufficient.

Typical forms:

* assuming compactness where only local compactness is given;
* using completeness without proving the space is complete;
* applying a theorem requiring smoothness, properness, Hausdorffness, separability, Noetherianity, finite generation, etc.;
* forgetting connectedness, orientability, irreducibility, nonzero characteristic restrictions, or boundary conditions.

Example pattern:

> “By the implicit function theorem…”
> but the derivative is not shown to be invertible at the relevant point, or the Banach-space version requires additional analytic hypotheses.

This is perhaps the most common serious error.

## 2. Quantifier mistakes

The proof silently changes the order or dependence of variables.

Common patterns:

* proving `∀x ∃ε` but later using a single `ε` for all `x`;
* choosing an object depending on `n`, then treating it as independent of `n`;
* extracting a subsequence depending on a parameter, then using it uniformly;
* confusing pointwise convergence with uniform convergence;
* proving something for each finite subset but using it for the whole infinite set without compactness or diagonalization.

A typical dangerous move is:

> “For every `x`, choose `N_x`. Taking `N` large enough…”

There may be no uniform `N`.

## 3. Boundary and degenerate cases

The main argument works only in the generic case.

Examples:

* dimension `0`, `1`, or `2` behaving differently;
* empty sets, zero objects, identity elements;
* reducible/singular/non-transverse cases;
* equality cases in inequalities;
* non-strict versus strict inequalities;
* endpoints of intervals;
* stabilizers or isotropy groups becoming nontrivial;
* rank dropping on a special locus.

Research proofs often handle the “open dense” or “generic” situation correctly but fail at degeneration.

## 4. Circular reasoning

A result is used, directly or indirectly, before it has been proved.

This can be subtle in long papers:

* Lemma A uses Proposition B;
* Proposition B uses Corollary C;
* Corollary C depends on Lemma A.

Or conceptually:

> “This construction is well-defined because it is invariant under the equivalence relation.”

but the invariance is essentially the theorem being proved.

## 5. Incorrect use of standard theorems

The proof invokes a familiar theorem outside its valid scope.

Examples:

* applying dominated convergence without an actual dominating function;
* applying Fubini/Tonelli without integrability or nonnegativity;
* using Zorn’s lemma without checking chains have upper bounds;
* invoking Sard’s theorem under insufficient differentiability;
* applying Nakayama’s lemma over the wrong kind of ring/module;
* using compactness in a non-Hausdorff setting;
* using spectral theory for unbounded operators while ignoring domains.

Often the cited theorem is morally relevant, but its exact hypotheses do not match.

## 6. “Obvious” maps not well-defined

A construction is described on representatives but not checked to descend to a quotient, localization, completion, colimit, moduli object, etc.

Common failures:

* independence of choice of representative;
* compatibility with transition maps;
* functoriality;
* naturality;
* equivariance;
* measurability or continuity;
* preservation of relations.

This is especially common in algebraic topology, category theory, representation theory, algebraic geometry, and geometric group theory.

## 7. Non-canonical choices treated as canonical

The proof chooses bases, splittings, identifications, metrics, triangulations, coordinates, representatives, or lifts, and then later argues as if the result is independent of those choices.

Typical issue:

> “Choose an isomorphism `V ≅ k^n`…”

Later the proof may use a construction that depends on this choice, even though the final statement is supposed to be invariant.

## 8. Confusing isomorphism with equality

Mathematicians often suppress canonical isomorphisms. Usually this is harmless, but sometimes it is not.

Dangerous cases include:

* identifying a space with its double dual;
* identifying products up to associativity without tracking coherence;
* confusing naturally isomorphic functors with equal functors;
* treating equivalent categories as literally identical;
* ignoring basepoints or markings;
* replacing an object by an isomorphic one in a context where extra structure matters.

In category-theoretic or formal settings, this becomes a major source of hidden errors.

## 9. False “without loss of generality”

A reduction is claimed but does not preserve the generality of the problem.

Examples:

* assuming a parameter is positive by symmetry when the situation is not symmetric;
* reducing to a dense subset without continuity;
* reducing to algebraically closed fields when descent is nontrivial;
* assuming diagonalizability or genericity;
* assuming a group action is free;
* assuming a matrix is in normal form but losing compatibility with other data.

A valid WLOG must include an invariance, reduction, approximation, or limiting argument.

## 10. Gaps in induction or recursion

Inductive proofs can fail in several ways:

* base case missing or wrong;
* induction hypothesis weaker than needed;
* induction step uses a stronger statement than proved;
* nested induction not well-founded;
* simultaneous induction not formulated correctly;
* recursion depends on data not shown to decrease.

In research mathematics, this often appears as “argue by complexity” without defining a well-founded complexity measure.

## 11. Hidden regularity or existence assumptions

A proof assumes the existence of an object that may not exist.

Examples:

* a minimizer exists, but only an infimum is known;
* a geodesic exists, but the space is not proper/complete;
* an extension exists, but no obstruction theory is checked;
* a solution to a PDE exists, but regularity is not established;
* a measurable selector exists, but selection hypotheses are absent.

This is common in analysis, geometry, dynamics, and probability.

## 12. Invalid limiting arguments

A statement is proved for approximations and then passed to the limit incorrectly.

Common failures:

* convergence is too weak to preserve the property;
* nonlinear operations do not commute with limits;
* constants are not uniform;
* compactness gives only subsequential convergence;
* the limiting object lies outside the intended class;
* regularity is lost in the limit.

A classic pattern:

> “Approximate by smooth objects and pass to the limit.”

This may fail unless the relevant estimates are uniform and the property is closed under the chosen topology.

## 13. Confusing local and global statements

A proof establishes a local result but concludes a global one.

Examples:

* local sections do not glue;
* local triviality does not imply global triviality;
* simply connectedness is silently assumed;
* a local coordinate construction has monodromy;
* transition functions are not checked;
* a local inverse exists but not a global inverse.

This is a major source of errors in geometry, topology, sheaf theory, and PDE.

## 14. Sign, orientation, and convention errors

These are “small” but can invalidate results.

Examples:

* orientation conventions in intersection theory;
* sign conventions in chain complexes;
* left versus right actions;
* covariant versus contravariant functoriality;
* inverse maps in group actions;
* grading shifts;
* Koszul signs;
* normalization of Fourier transforms or Laplacians.

Such errors are particularly common when comparing formulas across sources.

## 15. Ambiguous or overloaded notation

The same symbol is used for multiple objects, or notation hides dependence.

Examples:

* writing `C` for many different constants, then later needing uniformity;
* suppressing dependence on parameters;
* reusing `f` for induced maps at different levels;
* using the same norm/topology on different spaces;
* writing `≤` for different partial orders;
* using informal notation for equivalence classes.

This often causes genuine logical mistakes, not just exposition problems.

## 16. Diagram chasing errors

In homological algebra, category theory, and algebraic topology, diagrams can fail because:

* a square does not commute;
* a morphism has the wrong variance;
* exactness is used at the wrong object;
* a connecting morphism has the wrong sign;
* naturality is assumed but not proved;
* pullbacks and pushouts are confused.

These errors are easy to miss because the diagram “looks right”.

## 17. Misuse of genericity or measure-zero arguments

A property may hold generically, almost everywhere, or on a dense set, but the theorem needs it everywhere.

Examples:

* dense does not mean open;
* almost everywhere does not imply everywhere;
* residual does not imply full measure, and full measure does not imply residual;
* an exceptional set may depend on a parameter;
* countable intersections are okay in Baire arguments, uncountable intersections are not.

## 18. Algebraic manipulation errors

These still happen, especially inside long computations.

Examples:

* dropped terms;
* wrong signs;
* invalid cancellation in noncommutative settings;
* division by a possibly zero element;
* confusing left and right inverses;
* using an elementwise proof in a category where elements are unavailable;
* expanding a formula under assumptions that do not hold.

They are less conceptually interesting but often responsible for false lemmas.

## 19. Incorrect analogy or overgeneralization

A proof is modeled on a known case, but a crucial property does not generalize.

Examples:

* finite-dimensional intuition applied to infinite-dimensional spaces;
* commutative algebra intuition applied to noncommutative rings;
* smooth manifold arguments applied to singular spaces;
* Hilbert-space arguments applied to Banach spaces;
* discrete group arguments applied to locally compact groups;
* finite group averaging applied to infinite groups without amenability or measure.

This is a common source of plausible but false claims.

## 20. Expository compression hiding a real gap

A paper says:

> “It is clear that…”
> “A standard argument shows…”
> “By the usual compactness argument…”
> “After passing to a subsequence…”
> “One checks…”

Sometimes this is just brevity. Sometimes the omitted argument is nontrivial or false.

The danger is greatest when the omitted step involves:

* uniformity;
* gluing;
* functoriality;
* compactness;
* regularity;
* choice;
* limits;
* quotienting;
* exceptional cases.

## 21. Wrong statement, correct proof of a nearby theorem

Sometimes the argument proves a weaker or different theorem than the one stated.

Examples:

* proves existence but not uniqueness;
* proves injectivity but not surjectivity;
* proves result for smooth objects but states it for continuous ones;
* proves the theorem after replacing an object by a completion/localization/finite-index subgroup;
* proves a result up to isomorphism but states equality;
* proves a local classification but states global classification.

## 22. Computational or experimental misguidance

In modern work, computer algebra, numerical experiments, or examples may suggest a false conjecture.

Errors include:

* finite examples hiding infinite counterexamples;
* computations over small fields not reflecting characteristic zero;
* numerical evidence missing unstable modes;
* symbolic simplification assuming generic denominators nonzero;
* software defaults using different conventions.

This is not a proof error inside a proof, but often leads to erroneous claims.

## 23. Citation errors

A paper cites a known result that does not quite say what is needed.

Possibilities:

* the cited theorem has stronger hypotheses;
* the cited result proves a related but different statement;
* the citation depends on a convention incompatible with the present paper;
* the cited proof itself has a gap;
* the result is folklore and not available in the needed generality.

This is a common source of propagated errors.

## 24. Formalization-level errors

When translating proofs into Lean/Coq/Isabelle, additional hidden errors surface:

* implicit coercions are not canonical;
* universe levels matter;
* equality versus equivalence must be explicit;
* side conditions cannot be inferred;
* “obvious” well-definedness is missing;
* dependent types expose hidden choices;
* proof irrelevance or quotient reasoning is being used without justification.

Formalization does not merely check syntax; it often reveals places where the informal proof was under-specified.

---

A compact way to classify proof errors is:

| Error type             | Typical symptom                                           |
| ---------------------- | --------------------------------------------------------- |
| Hypothesis error       | A theorem is applied outside its assumptions              |
| Quantifier error       | A choice depends on something it later must not depend on |
| Degenerate-case error  | Generic argument fails at boundary/singular cases         |
| Construction error     | A map/object is not well-defined or not canonical         |
| Limit error            | Passage to a limit loses the needed property              |
| Local-global error     | Local data fail to glue globally                          |
| Circularity            | The proof uses what it is trying to prove                 |
| Notational suppression | Dependence, coherence, or equality is hidden              |
| Computation error      | Sign, factor, convention, or algebra mistake              |
| Citation error         | Referenced result is weaker/different than needed         |

For research mathematicians, the most dangerous errors are usually not arithmetic mistakes. They are failures of **uniformity**, **well-definedness**, **hidden hypotheses**, and **passage from local/generic/approximate statements to global/exact ones**.
