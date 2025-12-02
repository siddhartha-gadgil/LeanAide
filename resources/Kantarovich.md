Here is a formal proof of the local surjectivity result (a variation of the Kantorovich-Newton theorem) designed for formalization in Lean.

It relies on the **Banach Fixed Point Theorem** on a closed ball. We first state the necessary definitions and the fixed-point lemma, then proceed to the main proof by constructing an auxiliary function on $\mathbb{R}^m$.

---

### **Context and Definitions**

We assume the context of standard Euclidean spaces $\mathbb{R}^n$ and $\mathbb{R}^m$ equipped with the standard Euclidean norm $\|\cdot\|$.

**Definition 1 (Lipschitz Continuous Derivative):**
Let $U \subseteq \mathbb{R}^n$ be an open set. A differentiable function $f: U \to \mathbb{R}^m$ has a $K$-Lipschitz derivative if for all $x, y \in U$:
$$ \|Df(x) - Df(y)\|_{op} \le K \|x - y\| $$
where $\|\cdot\|_{op}$ denotes the operator norm.

**Lemma 1 (Banach Fixed Point Theorem on a Ball):**
Let $X$ be a Banach space (a complete normed vector space).
Let $x_c \in X$ and $r > 0$. Let $B = \{x \in X \mid \|x - x_c\| \le r\}$ be the closed ball of radius $r$ centered at $x_c$.
Let $\Psi: B \to X$ be a map satisfying the following conditions:
1.  **Contraction:** There exists a constant $0 \le \kappa < 1$ such that for all $u, v \in B$, $\|\Psi(u) - \Psi(v)\| \le \kappa \|u - v\|$.
2.  **Invariance:** For all $u \in B$, $\Psi(u) \in B$.

**Then:** There exists a fixed point $u^* \in B$ such that $\Psi(u^*) = u^*$.

---

### **Main Theorem**

**Assumptions:**
1.  Let $n, m$ be natural numbers with $n \ge 1, m \ge 1$.
2.  Let $f: \mathbb{R}^n \to \mathbb{R}^m$ be a differentiable function.
3.  Let $x_0 \in \mathbb{R}^n$ be a point in the domain.
4.  Let $\delta, M, K$ be real numbers strictly greater than 0.
5.  **Initial Bound:** Assume $\|f(x_0)\| < \delta$.
6.  **Right Inverse:** Assume $T: \mathbb{R}^m \to \mathbb{R}^n$ is a linear map such that $Df(x_0) \circ T = I_{\mathbb{R}^m}$ (the identity map on $\mathbb{R}^m$).
7.  **Inverse Bound:** Assume $\|T\|_{op} \le M$.
8.  **Regularity:** Assume $Df$ is $K$-Lipschitz in the open ball $B_{open}(x_0, 2M\delta)$.

**Hypothesis on $\delta$:**
Assume $\delta$ satisfies the condition:
$$ 4 M^2 K \delta \le 1 $$

**Goal:**
We aim to show that there exists an $x^* \in \mathbb{R}^n$ such that $\|x^* - x_0\| \le 2M\delta$ and $f(x^*) = 0$.

---

### **Proof**

#### **Step 1: Construction of the Auxiliary Function**

We proceed by reducing the problem to a fixed-point iteration in $\mathbb{R}^m$.
Let $\phi: \mathbb{R}^m \to \mathbb{R}^n$ be the affine map defined by:
$$ \phi(u) := x_0 + T(u) $$
Let $h: \mathbb{R}^m \to \mathbb{R}^m$ be the composition defined by:
$$ h(u) := f(\phi(u)) = f(x_0 + T(u)) $$
We aim to find a root of $h(u) = 0$. If $h(u^*) = 0$, then $x^* = x_0 + T(u^*)$ satisfies $f(x^*) = 0$.

#### **Step 2: Properties of the Auxiliary Function**

**Lemma 2 (Value at 0):**
By definition of $h$ and $\phi$, $h(0) = f(x_0 + T(0))$. Since $T$ is linear, $T(0) = 0$.
Thus, $h(0) = f(x_0)$.
By assumption (Initial Bound), $\|h(0)\| < \delta$.

**Lemma 3 (Derivative at 0):**
By the Chain Rule, the derivative of $h$ at $u$ is:
$$ Dh(u) = Df(\phi(u)) \circ D\phi(u) $$
Since $\phi(u) = x_0 + T(u)$ is affine, its derivative is the linear map $T$.
$$ Dh(u) = Df(x_0 + T(u)) \circ T $$
At $u = 0$:
$$ Dh(0) = Df(x_0) \circ T $$
By assumption (Right Inverse), $Df(x_0) \circ T = I_{\mathbb{R}^m}$.
Thus, $Dh(0) = I_{\mathbb{R}^m}$.

**Lemma 4 (Lipschitz Constant of $Dh$):**
Let $u_1, u_2 \in \mathbb{R}^m$.
By the definition of the operator norm and composition:
$$ \|Dh(u_1) - Dh(u_2)\|_{op} = \| (Df(\phi(u_1)) - Df(\phi(u_2))) \circ T \|_{op} $$
$$ \|Dh(u_1) - Dh(u_2)\|_{op} \le \| Df(\phi(u_1)) - Df(\phi(u_2)) \|_{op} \| T \|_{op} $$
By assumption (Regularity), $Df$ is $K$-Lipschitz.
$$ \|Dh(u_1) - Dh(u_2)\|_{op} \le K \| \phi(u_1) - \phi(u_2) \| \| T \|_{op} $$
Since $\phi(u_1) - \phi(u_2) = T(u_1 - u_2)$:
$$ \|Dh(u_1) - Dh(u_2)\|_{op} \le K \| T(u_1 - u_2) \| M $$
$$ \|Dh(u_1) - Dh(u_2)\|_{op} \le K (M \| u_1 - u_2 \|) M $$
$$ \|Dh(u_1) - Dh(u_2)\|_{op} \le (K M^2) \| u_1 - u_2 \| $$
Let $L := K M^2$. Then $Dh$ is $L$-Lipschitz.

#### **Step 3: Setup for Banach Fixed Point Theorem**

Let $r := 2\delta$.
Let $B_{\mathbb{R}^m} = \{ u \in \mathbb{R}^m \mid \|u\| \le r \}$ be the closed ball of radius $r$ centered at $0$ in $\mathbb{R}^m$.

Define the map $\Psi: B_{\mathbb{R}^m} \to \mathbb{R}^m$ by:
$$ \Psi(u) := u - h(u) $$
A fixed point $\Psi(u) = u$ implies $h(u) = 0$.

We verify the conditions for Lemma 1 (Banach Fixed Point Theorem).

**Condition 1: Contraction**
We bound the derivative $D\Psi(u)$.
$$ D\Psi(u) = I_{\mathbb{R}^m} - Dh(u) = Dh(0) - Dh(u) $$
Taking norms:
$$ \|D\Psi(u)\|_{op} = \|Dh(0) - Dh(u)\|_{op} $$
Using Lemma 4 (Lipschitz property of $Dh$):
$$ \|D\Psi(u)\|_{op} \le L \|0 - u\| = M^2 K \|u\| $$
For any $u \in B_{\mathbb{R}^m}$, we have $\|u\| \le r = 2\delta$.
$$ \|D\Psi(u)\|_{op} \le M^2 K (2\delta) = 2 M^2 K \delta $$
By the hypothesis on $\delta$ ($4 M^2 K \delta \le 1$), we have $2 M^2 K \delta \le \frac{1}{2}$.
Thus, for all $u \in B_{\mathbb{R}^m}$, $\|D\Psi(u)\|_{op} \le \frac{1}{2}$.
By the Mean Value Inequality, for any $u, v \in B_{\mathbb{R}^m}$:
$$ \|\Psi(u) - \Psi(v)\| \le \sup_{w \in B_{\mathbb{R}^m}} \|D\Psi(w)\|_{op} \|u - v\| \le \frac{1}{2} \|u - v\| $$
This proves $\Psi$ is a contraction with constant $\kappa = \frac{1}{2}$.

**Condition 2: Invariance**
We must show that if $u \in B_{\mathbb{R}^m}$, then $\Psi(u) \in B_{\mathbb{R}^m}$.
$$ \|\Psi(u)\| = \|\Psi(u) - \Psi(0) + \Psi(0)\| $$
By the triangle inequality:
$$ \|\Psi(u)\| \le \|\Psi(u) - \Psi(0)\| + \|\Psi(0)\| $$
From the contraction property (Condition 1):
$$ \|\Psi(u) - \Psi(0)\| \le \frac{1}{2} \|u - 0\| = \frac{1}{2}\|u\| \le \frac{1}{2}r $$
For the term $\|\Psi(0)\|$:
$$ \Psi(0) = 0 - h(0) = -h(0) $$
By Lemma 2, $\|h(0)\| < \delta$.
Recall we defined $r = 2\delta$, so $\delta = \frac{1}{2}r$.
$$ \|\Psi(0)\| < \frac{1}{2}r $$
Combining these results:
$$ \|\Psi(u)\| < \frac{1}{2}r + \frac{1}{2}r = r $$
Thus, $\|\Psi(u)\| \le r$, so $\Psi(u) \in B_{\mathbb{R}^m}$.

#### **Step 4: Conclusion**

Since $B_{\mathbb{R}^m}$ is a closed ball in a complete space (Euclidean space is Banach), and $\Psi$ satisfies the Contraction and Invariance conditions, by Lemma 1 there exists $u^* \in B_{\mathbb{R}^m}$ such that $\Psi(u^*) = u^*$.

This implies $u^* - h(u^*) = u^*$, which yields $h(u^*) = 0$.

Define $x^* := \phi(u^*) = x_0 + T(u^*)$.
Then $f(x^*) = f(\phi(u^*)) = h(u^*) = 0$.

Finally, we verify $x^*$ is in the required neighborhood.
$$ \|x^* - x_0\| = \|T(u^*)\| \le \|T\|_{op} \|u^*\| $$
Since $\|T\|_{op} \le M$ and $u^* \in B_{\mathbb{R}^m}$ (so $\|u^*\| \le r = 2\delta$):
$$ \|x^* - x_0\| \le M (2\delta) = 2M\delta $$

Therefore, there exists an $x$ (specifically $x^*$) in the neighborhood of $x_0$ such that $f(x) = 0$.

**Q.E.D.**
