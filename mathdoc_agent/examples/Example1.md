 ## Theorem :

A group G satisfying (a*b)^2 = a^2*b^2 for all a, b in G is Abelian

## Proof:
Let $G$ be a group such that for all $a,b \in G$ we have
\[
(ab)^2 = a^2 b^2.
\]
By the definition of the group operation, this identity means
\[
abab = aabb
\]
for all $a,b \in G$.

Fix arbitrary elements $a,b \in G$. We want to prove that $ab = ba$. Since $abab = aabb$, we can manipulate this equality using the group axioms.

First, multiply both sides on the left by $a^{-1}$. Using associativity of the group operation, this gives
\[
a^{-1}(abab) = a^{-1}(aabb).
\]
Rewriting each side using associativity:
\[
(a^{-1}a)bab = (a^{-1}a)abb.
\]
Since $a^{-1}a = e$, where $e$ is the identity element of $G$, this simplifies to
\[
ebab = eabb,
\]
so
\[
bab = abb.
\]

Next, multiply both sides of this new equality on the right by $b^{-1}$. Using associativity again, we obtain
\[
(bab)b^{-1} = (abb)b^{-1}.
\]
Rewriting each side:
\[
ba(bb^{-1}) = ab(b b^{-1}).
\]
Since $bb^{-1} = e$, this becomes
\[
ba e = ab e.
\]
Because $xe = x$ for all $x \in G$, we have
\[
ba = ab.
\]

Since $a$ and $b$ were arbitrary elements of $G$, this shows that $ab = ba$ for all $a,b \in G$. Therefore $G$ is Abelian.