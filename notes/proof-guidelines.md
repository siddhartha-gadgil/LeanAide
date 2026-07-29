# Proof guidelines for Lean-oriented source documents

These guidelines are intended for source text and proof-generation prompts
that will later be translated to JSON and then to Lean.  The goal is not to
write Lean code in the source document, but to give enough formal structure
that the translation pipeline can recover Lean-checkable proof steps.

## General rules

1. State every variable with its type and scope before using it.  Distinguish
   `Nat`, positive `Nat`, `Int`, positive `Int`, and real coercions.
2. Use explicit function application: write `f(m, k)` or `f m k`, not
   "f applied to m and k".
3. Use explicit multiplication in noncommutative groups: write `x^m * c^k`,
   not `x^m c^k`.
4. Avoid mixed relation chains as single claims.  Split
   `A = B <= C = D` into separate claims `A = B`, `B <= C`, and `C = D`.
5. Do not assert a final target before proving the intermediate lemma that
   establishes it.  If a proof first proves `P` by a subargument, introduce
   that subargument explicitly and only then conclude `P`.
6. Do not reassert local hypotheses as new proof obligations.  If `h : P` is
   already assumed, say "use the hypothesis `h`" rather than "prove `P`".
7. When applying a previous lemma, give the intended instantiation of every
   non-obvious argument and every required hypothesis.

## Local definitions and scope

1. Give local definitions with explicit types.

   Example:

   ```text
   Define C : Nat -> G by C n = (w * y)^n * s^{-1} * t * (z * w^{-1})^n.
   ```

2. After defining a local object, use its name directly.  Do not repeatedly
   restate the defining equality unless the equality itself is needed.
3. If a local definition depends on variables, state where those variables are
   fixed.  For example, if `m k : Int` are fixed, every later claim involving
   `m` and `k` should remain under that same scope.
4. Avoid changing the type of a local function in later proof steps.  If
   `f : Int -> Int -> Real`, every claim using `f` must keep the same type.

## Induction proofs

1. State the induction variable and its type.
2. State the induction hypothesis exactly.
3. In the induction step, identify which line uses the induction hypothesis.
4. Keep the successor statement in the same type as the induction variable.
   For `n : Nat`, use `n + 1`; for `n : Int`, explain why induction is
   available or avoid induction on `Int`.
5. Separate algebraic recurrence, application of a previous lemma, triangle
   inequality, use of the induction hypothesis, and final arithmetic into
   separate claims.

## Conjugacy and group calculations

1. Do not write only "`a` is conjugate to `b`" unless a formal conjugacy
   predicate has already been chosen.  Prefer an explicit conjugating element:

   ```text
   a = g * b * g^{-1}.
   ```

2. If equality implies conjugacy, still give the explicit equation using the
   identity conjugator:

   ```text
   a = 1 * b * 1^{-1}.
   ```

3. When using conjugation invariance, give the exact term:

   ```text
   Apply Lemma 1 with x := b and y := g to the equation a = g * b * g^{-1}.
   ```

4. For powers of conjugates, state the exact theorem shape needed, including
   the exponent type:

   ```text
   For n : Int, (g * x * g^{-1})^n = g * x^n * g^{-1}.
   ```

5. For noncommutative group simplifications, avoid saying "by rearranging"
   unless only associativity and inverse cancellation are used.  State the
   concrete equality to be proved.

## Inequalities and arithmetic

1. State every positivity side condition used for division or cancellation.
   For example, if dividing by `n`, specify whether the positive real scalar
   is `(n : Real)` or `(2 * n : Real)`.
2. Separate order reasoning from algebraic simplification.  First prove the
   inequality by monotonicity/transitivity; then prove the arithmetic identity
   that rewrites the right-hand side.
3. If a proof uses nonnegativity of a length, state the exact instance:

   ```text
   By pseudo-length nonnegativity, 0 <= l(s) and 0 <= l(t).
   ```

4. For casts, specify them in prose:

   ```text
   Regard n : Nat as a real number in the term (n : Real) * (l y + l z).
   ```

## Limit and Archimedean arguments

Limit arguments should be factored into a separately stated lemma whenever
possible.  Do not leave them as "let n tend to infinity" unless the named
lemma is already available.

Useful theorem shape:

```text
If A B C : Real, 0 <= C, and for every positive natural number n,
A <= B + C / n, then A <= B.
```

For each use, state:

1. the values of `A`, `B`, and `C`;
2. the proof that `0 <= C`;
3. the previously proved family of inequalities;
4. the conclusion obtained by the lemma.

If the proof instead uses filters or sequences, state the filter and sequence
explicitly and name the convergence theorem being used.

## Good proof-step shape

Prefer proof steps of this form:

```text
Claim h_step:
  C (n + 1) = w * (y * C n * z) * w^{-1}.
Reason:
  Expand the definition of C, use pow_succ, associativity, and inverse
  cancellation. No commutativity is used.
```

Avoid proof steps of this form:

```text
Clearly the recurrence holds by simplification.
```

The first form gives the translator a single Lean proposition, its local name,
and the permitted proof ingredients.  The second form leaves too much proof
planning to later automation.
