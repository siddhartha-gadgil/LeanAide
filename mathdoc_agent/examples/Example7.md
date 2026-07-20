## Theorem :

The co-countable topology on a set $X$ is defined such that $U$ is open if $U = \emptyset$ or $X \setminus U$ is countable.
Let $X$ be an uncountable set equipped with the co-countable topology. Prove that a sequence $(x_n)$ in $X$ converges to a point $L \in X$ if and only if the sequence is "eventually constant" (i.e., there exists an integer $N$ such that for all $n \ge N$, $x_n = L$).

## Proof :

Let $X$ be an uncountable set equipped with the co-countable topology, so a subset $U \subseteq X$ is open if and only if either $U = \emptyset$ or $X \setminus U$ is countable.

Let $(x_n)_{n \in \mathbb{N}}$ be a sequence in $X$, and let $L \in X$.

To say that $(x_n)$ converges to $L$ in this topology means:

For every open set $U \subseteq X$ with $L \in U$, there exists $N \in \mathbb{N}$ such that for all $n \ge N$, $x_n \in U$.

The sequence $(x_n)$ is eventually constant with value $L$ if:

There exists $N \in \mathbb{N}$ such that for all $n \ge N$, $x_n = L$.

The goal is to show that $(x_n)$ converges to $L$ if and only if $(x_n)$ is eventually constant with value $L$.

---

First, assume that $(x_n)$ converges to $L$. Define the subset
\[
A := \{x_n \mid n \in \mathbb{N},\ x_n \neq L\} \subseteq X.
\]
The set $A$ is the set of all values taken by the sequence which are different from $L$.

Since the sequence $(x_n)$ is indexed by $\mathbb{N}$, the set of all values $\{x_n \mid n \in \mathbb{N}\}$ is at most countable. Therefore $A$ is a subset of a countable set, hence $A$ is countable.

Consider the set
\[
U := X \setminus A.
\]
Since $A$ is countable, its complement $U$ is open in the co-countable topology. Furthermore, $L \notin A$ by definition of $A$ (every element of $A$ is different from $L$), hence $L \in U$.

Because $(x_n)$ converges to $L$, and $U$ is an open set containing $L$, there exists some $N \in \mathbb{N}$ such that for all $n \ge N$, $x_n \in U$.

By the definition of $U = X \setminus A$, the condition $x_n \in U$ is equivalent to $x_n \notin A$, which means $x_n = L$ (since the only values excluded from $U$ are those in $A$, i.e., those not equal to $L$). Thus, for all $n \ge N$, we have $x_n = L$.

This shows that the sequence $(x_n)$ is eventually constant with value $L$.

---

Conversely, assume that the sequence $(x_n)$ is eventually constant with value $L$. Then there exists $N \in \mathbb{N}$ such that for all $n \ge N$, $x_n = L$.

Let $U \subseteq X$ be any open set such that $L \in U$. We must show that there exists $M \in \mathbb{N}$ such that for all $n \ge M$, $x_n \in U$.

By assumption, for all $n \ge N$, we have $x_n = L$. Since $L \in U$, it follows that for all $n \ge N$, $x_n \in U$. Thus we can take $M = N$.

Therefore, for every open set $U$ containing $L$, there exists $M$ such that for all $n \ge M$, $x_n \in U$, which means that $(x_n)$ converges to $L$ in the co-countable topology.

---

Combining both directions, the sequence $(x_n)$ converges to $L$ if and only if it is eventually constant with value $L$.