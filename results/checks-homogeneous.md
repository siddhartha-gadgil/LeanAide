# Checks for `results/homogeneous.md`

This file records checks of `results/homogeneous.md` against the error patterns
in `notes/maths-errors.md` and the stress tests in `notes/maths-stress-tests.md`.

## Corrections made during checking

1. **Splitting lemma application.**
   In the commutator recurrence, the use of the splitting lemma was made
   explicit.  The application is with
   $s=e$, $t=y$, the splitting element $w=x$, and the two remainder terms
   $u=x^{m-1}c^k$ and $v=y^{-1}x^m c^{k-1}xy$.

2. **Passage from rational seminorm to real Banach space.**
   The previous proof hid the construction of the real Banach space behind an
   "extend scalars" sentence.  This was replaced by a direct construction:
   first quotient by the zero-seminorm subspace, then complete the resulting
   normed rational vector space, and define real scalar multiplication by
   rational approximation.  The proof now includes the Cauchy estimate needed
   for well-definedness.

3. **Embedding of a torsion-free abelian group into a real vector space.**
   The converse direction of the corollary now factors the injectivity through
   the localization map $G\to G\otimes_{\mathbb Z}\mathbb Q$, then extends
   scalars from $\mathbb Q$ to $\mathbb R$.

## Error-pattern checks

1. **Missing hypotheses.**
   The proof uses homogeneity in the conjugation-invariance lemma, the
   splitting lemma, the torsion argument, and the final length construction.
   It uses nonnegativity when deriving $l(c)=0$ from $l(c)\leq 0$ and when
   proving products of zero-length commutators have zero length.

2. **Quantifier dependence.**
   The limiting arguments in Lemmas 1 and 3 keep the auxiliary positive integer
   independent of the fixed group elements.  The constants depending on the
   fixed elements are divided by $n$ and vanish as $n\to\infty$.

3. **Boundary cases.**
   Lemma 5 allows $n=0$, but Proposition 7 only divides by positive integers.
   Negative powers are covered by homogeneity over all integers.  The trivial
   group and abelian groups cause no special case failure.

4. **Well-defined quotient and localization maps.**
   The descent to the abelianization is checked by representative independence.
   The descent through torsion uses the same argument after proving torsion has
   zero length.  The rational extension checks independence of the
   representation $a/n$.

5. **Sign and convention checks.**
   With the convention $[x,y]=xyx^{-1}y^{-1}$, the commutator recurrence uses
   $xyx^{-1}=cy$ and obtains the endpoint
   $(S_{2n},-S_{2n}/2)$ after $2n$ recurrence steps.

6. **Limiting arguments.**
   The only limits are elementary real limits: constants divided by positive
   integers tend to zero, and $\sqrt{2n}/n$ tends to zero.  No compactness or
   subsequence argument is used.

## Stress tests passed

1. **Hypothesis weakening.**
   Removing homogeneity breaks the proof at Lemma 1.  This is expected: ordinary
   word lengths on nonabelian groups need not vanish on commutators.

2. **Conclusion strengthening.**
   The proof does not show that every homogeneous pseudo-length is a length
   function.  The zero function on any group remains a counterexample, and the
   proof correctly factors through a seminorm before applying the separate
   positivity hypothesis.

3. **Boundary-case test for torsion.**
   On a finite cyclic group, any homogeneous pseudo-length vanishes because
   $g^n=e$ implies $n\,l(g)=0$.  Thus no homogeneous length exists unless the
   group is trivial, matching the corollary.

4. **Abelian torsion-free sanity test.**
   For $G=\mathbb Z^r$, the converse construction reduces to choosing a norm on
   $\mathbb R^r$ and restricting it to the lattice, which gives the expected
   homogeneous length.

5. **Nonabelian stress test.**
   If a homogeneous length existed on a nonabelian group, Proposition 7 would
   force every commutator to be the identity because nonidentity elements have
   positive length.  Hence the proof breaks the false strengthened claim exactly
   at the commutator-vanishing step.

6. **Parameter-dependence test for the random walk.**
   The random variables in Lemma 5 depend only on the chosen positive integer
   $n$.  The endpoint calculation keeps both coordinates and does not replace
   $f(S_{2n},-S_{2n}/2)$ by the stronger and generally false
   $f(S_{2n},0)$.

After the corrections above, no remaining failure from the listed error
patterns or stress tests was found.
